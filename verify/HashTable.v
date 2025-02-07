Require Import Uint63.
Require Import PArray.
Require Import List.
Require Import Lia.
Require Import ZArith.
From BusyCoq Require Import LibTactics.
From BusyCoq Require Export Eqb.

Module HashConcat.
Open Scope uint63.
Definition hash_t:Type := int*int.

Definition hash_P:int := 1234577.
Definition hash_v1:int := 293999.

Definition hash_concat(a b:hash_t):hash_t :=
let '(a0,a1):=a in
let '(b0,b1):=b in
(a0*b1+b0,a1*b1).

Definition hv1:hash_t := Eval compute in (hash_v1*1,hash_P).
Definition hv2:hash_t := Eval compute in (hash_v1*2,hash_P).
Definition hv3:hash_t := Eval compute in (hash_v1*3,hash_P).
Definition hv4:hash_t := Eval compute in (hash_v1*4,hash_P).
Definition hv5:hash_t := Eval compute in (hash_v1*5,hash_P).
Definition hv6:hash_t := Eval compute in (hash_v1*6,hash_P).
Definition hv7:hash_t := Eval compute in (hash_v1*7,hash_P).
Definition hv8:hash_t := Eval compute in (hash_v1*8,hash_P).
Definition hv9:hash_t := Eval compute in (hash_v1*9,hash_P).
Definition hv10:hash_t := Eval compute in (hash_v1*10,hash_P).
Definition hv11:hash_t := Eval compute in (hash_v1*11,hash_P).
Definition hv12:hash_t := Eval compute in (hash_v1*12,hash_P).
Definition hv13:hash_t := Eval compute in (hash_v1*13,hash_P).
Definition hv14:hash_t := Eval compute in (hash_v1*14,hash_P).
Definition hv15:hash_t := Eval compute in (hash_v1*15,hash_P).
Definition hv16:hash_t := Eval compute in (hash_v1*16,hash_P).

Notation "a ## b" := (hash_concat a b) (at level 50, left associativity).
Notation "a # b" := (a*hash_P+b)%uint63 (at level 50, left associativity).

Fixpoint Pos_hash'(x:positive) h :=
match x with
| xH => h
| xI x0 => Pos_hash' x0 (hv2 ## h)
| xO x0 => Pos_hash' x0 (hv3 ## h)
end.

Definition Pos_hash(x:positive) := Pos_hash' x hv1.

Definition N_hash(x:N) :=
match x with
| N0 => hv1
| Npos x0 => hv2 ## Pos_hash x0
end.

Definition Z_hash(x:Z) :=
match x with
| Z0 => hv1
| Zpos x0 => hv2 ## Pos_hash x0
| Zneg x0 => hv3 ## Pos_hash x0
end.

Fixpoint list_hash'{A}(f:A->_)(ls:list A) h:=
match ls with
| nil => h
| a::ls0 => list_hash' f ls0 (hv1 ## f a ## h)
end.

Definition list_hash{A} f (ls:list A) := list_hash' f ls hv2.

Definition prod_hash{A B} f g (x:A*B) :=
  let (a,b):=x in hv1 ## (f a) ## (g b).

Definition sum_hash{A B} f g (x:A+B) :=
  match x with
  | inl x0 => hv1 ## f x0
  | inr x1 => hv2 ## g x1
  end.

Definition option_hash{A} f (x:option A) :=
  match x with
  | Some x0 => hv1 ## f x0
  | None => hv2
  end.

Definition bool_hash(x:bool) :=
match x with
| true => hv1
| false => hv2
end.

Class Hash A := {
  hash : A -> (int*int)
}.

#[export] Instance bool_Hash: Hash bool := (ltac: (split; apply bool_hash)).
#[export] Instance positive_Hash: Hash positive := (ltac: (split; apply Pos_hash)).
#[export] Instance N_Hash: Hash N := (ltac: (split; apply N_hash)).
#[export] Instance Z_Hash: Hash Z := (ltac: (split; apply Z_hash)).
#[export] Instance list_Hash A: Hash A -> Hash (list A) := (ltac: (esplit; apply list_hash,hash)).
#[export] Instance prod_Hash A B: Hash A -> Hash B -> Hash (A*B) := (ltac: (esplit; apply prod_hash; apply hash)).
#[export] Instance sum_Hash A B: Hash A -> Hash B -> Hash (A+B) := (ltac: (esplit; apply sum_hash; apply hash)).
#[export] Instance option_Hash A: Hash A -> Hash (option A) := (ltac: (esplit; apply option_hash; apply hash)).


End HashConcat.



Module Type HashableType.
Parameter K:Type.
Parameter K_hash:K->(int*int).
Parameter K_eq:K->K->bool.
Parameter K_eq_spec:forall a b, Bool.reflect (a=b) (K_eq a b).
End HashableType.

Module ListHash(A:HashableType) <: HashableType.
Import HashConcat.
Definition K:Type := list A.K.
Definition K_hash(x:K):int*int := list_hash A.K_hash x.
Definition K_eq := list_eqb A.K_eq.
Definition K_eq_spec a b := list_eqb_spec A.K_eq a b A.K_eq_spec.
End ListHash.

Module ProdHash(A:HashableType)(B:HashableType) <: HashableType.
Import HashConcat.
Definition K:Type := A.K*B.K.
Definition K_hash(x:K):int*int :=
  let '(a,b):=x in
  A.K_hash a ## B.K_hash b.
Definition K_eq := prod_eqb A.K_eq B.K_eq.
Definition K_eq_spec a b := prod_eqb_spec A.K_eq B.K_eq a b A.K_eq_spec B.K_eq_spec.
End ProdHash.

Module Type ValueType.
Parameter V:Type.
End ValueType.

Module HashMap(KeyType:HashableType)(ValueType:ValueType).
Export KeyType.
Export ValueType.
Definition hmap_t := array (list (K*V*int)).

Open Scope uint63.

Definition hmap_make(len:int):hmap_t :=
  make (if len=?0 then 1 else len) nil.

Fixpoint hmap_entry_set(ls:list (K*V*int))(k:K)(v:V)(x:int) :=
match ls with
| nil => (k,v,x)::nil
| ((k',v',x') as h)::t =>
    if (if (x' =? x) then (K_eq k' k) else false) then (k,v,x)::t
    else h::(hmap_entry_set t k v x)
end.

Fixpoint hmap_entry_get(ls:list (K*V*int))(k:K)(x:int) :=
match ls with
| nil => None
| ((k',v',x') as h)::t =>
    if (if (x' =? x) then (K_eq k' k) else false) then Some v'
    else hmap_entry_get t k x
end.

Definition hmap_set(k:K)(v:V)(c:hmap_t):hmap_t :=
let x:=fst (K_hash k) in
let p:=(x mod (PArray.length c)) in
c.[p<-hmap_entry_set c.[p] k v x].

Definition hmap_get(k:K)(c:hmap_t):option V :=
let x:=fst (K_hash k) in
let p:=(x mod (PArray.length c)) in
hmap_entry_get c.[p] k x.

Definition hmap_set'(k:K)(v:V)(c:hmap_t) x p:hmap_t :=
c.[p<-hmap_entry_set c.[p] k v x].

Definition hmap_get'(k:K)(c:hmap_t) x p:option V :=
hmap_entry_get c.[p] k x.

Definition hmap_WF(c:hmap_t):Prop :=
  (0 <? (PArray.length c)) = true.

Lemma hmap_make_WF len:
  hmap_WF (hmap_make len).
Proof.
  unfold hmap_WF.
  cbn.
  rewrite length_make.
  destruct (len =? 0) eqn:E.
  1: reflexivity.
  destruct (len ≤? max_length).
  2: reflexivity.
  rewrite ltb_spec.
  destruct (eqbP len 0) as [E0|E0].
  1: congruence.
  pose proof (to_Z_bounded len).
  change (to_Z 0) with BinInt.Z0.
  change (to_Z 0) with BinInt.Z0 in E0.
  lia.
Qed.

Lemma hmap_set_WF k v c:
  hmap_WF c ->
  hmap_WF (hmap_set k v c).
Proof.
  unfold hmap_WF.
  intros H.
  unfold hmap_set.
  rewrite length_set.
  apply H.
Qed.

Lemma hmap_get_set_same k v c:
  hmap_WF c ->
  hmap_get k (hmap_set k v c) = Some v.
Proof.
  intros Hwf.
  unfold hmap_WF in Hwf.
  rewrite ltb_spec in Hwf.
  unfold hmap_get,hmap_set.
  rewrite length_set.
  remember (fst (K_hash k) mod PArray.length c) as x.
  rewrite get_set_same.
  2:{
    rewrite Heqx.
    rewrite ltb_spec.
    rewrite mod_spec.
    apply BinInt.Z.mod_pos_bound.
    apply Hwf.
  }
  induction c.[x] as [|[[k0 v0] x0] t].
  - cbn.
    rewrite eqb_refl.
    destruct (K_eq_spec k k); trivial; congruence.
  - cbn.
    destruct (x0 =? fst (K_hash k)) eqn:Ex0k.
    + destruct (K_eq_spec k0 k) as [Ek0|Ek0].
      * cbn.
        rewrite eqb_refl.
        destruct (K_eq_spec k k); congruence.
      * cbn.
        rewrite Ex0k.
        destruct (K_eq_spec k0 k); congruence.
    + cbn.
      rewrite Ex0k.
      apply IHt.
Qed.

Lemma hmap_get_set_other k k' v c:
  hmap_WF c ->
  k<>k' ->
  hmap_get k (hmap_set k' v c) = hmap_get k c.
Proof.
  intros Hwf.
  unfold hmap_WF in Hwf.
  rewrite ltb_spec in Hwf.
  unfold hmap_get,hmap_set.
  rewrite length_set.
  remember (fst (K_hash k') mod PArray.length c) as x'.
  remember (fst (K_hash k) mod PArray.length c) as x.
  intros Hne.
  destruct (eq_dec x x').
  2: rewrite get_set_other; auto.
  clear Heqx'. subst x'.
  rewrite get_set_same.
  2:{
    rewrite Heqx.
    rewrite ltb_spec.
    rewrite mod_spec.
    apply BinInt.Z.mod_pos_bound.
    apply Hwf.
  }
  induction c.[x] as [|[[k0 v0] x0] t].
  - cbn.
    destruct (fst (K_hash k') =? fst (K_hash k)); trivial.
    destruct (K_eq_spec k' k); trivial.
    congruence.
  - cbn.
    cbn in IHt.
    destruct (x0 =? fst (K_hash k')) eqn:Ex0k'.
    + destruct (K_eq_spec k0 k') as [Ek0|Ek0].
      * destruct (x0 =? fst (K_hash k)) eqn:Ex0k.
        -- cbn.
          rewrite Uint63.eqb_spec in Ex0k,Ex0k'.
          rewrite <-Ex0k,Ex0k'.
          rewrite eqb_refl,Ek0.
          destruct (K_eq_spec k' k); congruence.
        -- cbn.
          destruct (fst (K_hash k') =? fst (K_hash k)) eqn:Ek'k.
          2: reflexivity.
          rewrite Uint63.eqb_spec in Ex0k',Ek'k.
          rewrite eqb_false_spec in Ex0k.
          congruence.
      * cbn.
        destruct (x0 =? fst (K_hash k)) eqn:Ex0k; auto.
        destruct (K_eq_spec k0 k) as [Ek1|Ek1]; auto.
    + cbn.
      destruct (x0 =? fst (K_hash k)) eqn:Ex0k; auto.
      destruct (K_eq_spec k0 k) as [Ek1|Ek1]; auto.
Qed.

Lemma hmap_get_make k len:
  hmap_get k (hmap_make len) = None.
Proof.
  cbn.
  rewrite get_make.
  reflexivity.
Qed.

Definition hmap_upd2{T}(k:K)(f:option V->V*T)(c:hmap_t):hmap_t*T :=
let x:=fst (K_hash k) in
let p:=(x mod (PArray.length c)) in
let (v,t):=(f (hmap_get' k c x p)) in
(hmap_set' k v c x p,t).

Lemma hmap_upd2_spec{T} k (f:option V->V*T) c:
  hmap_upd2 k f c =
  let (v,t):=(f (hmap_get k c)) in
  (hmap_set k v c,t).
Proof.
  reflexivity.
Qed.

Definition hmap_upd(k:K)(f:option V->V)(c:hmap_t):hmap_t :=
let x:=fst (K_hash k) in
let p:=(x mod (PArray.length c)) in
(hmap_set' k (f (hmap_get' k c x p)) c x p).

Lemma hmap_upd_spec k f c:
  hmap_upd k f c =
  (hmap_set k (f (hmap_get k c)) c).
Proof.
  reflexivity.
Qed.

Definition hmap_add(k:K)(v:V)(c:hmap_t):option hmap_t :=
let x:=fst (K_hash k) in
let p:=(x mod (PArray.length c)) in
match hmap_get' k c x p with
| None =>
  Some (hmap_set' k v c x p)
| Some _ => None
end.

Lemma hmap_add_spec k v c:
hmap_add k v c =
match hmap_get k c with
| None => Some (hmap_set k v c)
| Some _ => None
end.
Proof.
  reflexivity.
Qed.


Section Cached.
Hypothesis f:K->V.
Definition hmap_get_cached'(k:K)(c:hmap_t):V*hmap_t :=
match hmap_get k c with
| Some v => (v,c)
| None =>
  let v := f k in
  (v,hmap_set k v c)
end.

Definition hmap_get_cached(k:K)(c:hmap_t):V*hmap_t :=
let x:=fst (K_hash k) in
let p:=(x mod (PArray.length c)) in
match hmap_get' k c x p with
| Some v => (v,c)
| None =>
  let v := f k in
  (v,hmap_set' k v c x p)
end.

Definition cache_WF(c:hmap_t):Prop :=
hmap_WF c /\
forall k,
match hmap_get k c with
| None => True
| Some v => v = f k
end.


Lemma hmap_get_cached'_spec k c:
  hmap_get_cached k c =
  hmap_get_cached' k c.
Proof.
  reflexivity.
Qed.

Lemma hmap_get_cached_spec k c:
  cache_WF c ->
  let '(v,c') := hmap_get_cached k c in
  v = f k /\
  cache_WF c'.
Proof.
  unfold cache_WF.
  intros [Hwf1 Hwf2].
  rewrite hmap_get_cached'_spec.
  unfold hmap_get_cached'.
  destruct (hmap_get k c) eqn:E.
  - pose proof (Hwf2 k) as Hwf.
    rewrite E in Hwf.
    tauto.
  - split.
    1: reflexivity.
    split.
    1: apply hmap_set_WF,Hwf1.
    intros k0.
    destruct (K_eq_spec k0 k).
    1: subst k0; rewrite hmap_get_set_same; auto.
    rewrite hmap_get_set_other; auto.
    apply Hwf2.
Qed.

Lemma hmap_make_cache_WF len:
  cache_WF (hmap_make len).
Proof.
  split.
  1: apply hmap_make_WF.
  intros k.
  rewrite hmap_get_make; trivial.
Qed.
End Cached.
End HashMap.


Module Uint63_K <: HashableType.
Definition K := int.
Definition K_hash(x:int) := (x,HashConcat.hash_P).
Definition K_eq := Uint63.eqb.
Lemma K_eq_spec x y: Bool.reflect (x=y) (Uint63.eqb x y).
Proof.
  destruct (Uint63.eqb x y) eqn:E.
  - rewrite Uint63.eqb_spec in E.
    constructor.
    apply E.
  - rewrite eqb_false_spec in E.
    constructor.
    apply E.
Qed.
End Uint63_K.

Module Uint63_V <: ValueType.
Definition V := int.
End Uint63_V.

Module IdAlloc(K_t:HashableType).
Export K_t.

Module V_t <: ValueType.
Definition V := K.
End V_t.

Module MapToId := HashMap K_t Uint63_V.
Module MapFromId := HashMap Uint63_K V_t.
Import ZArith.

Definition id_alloc_t:Type := MapToId.hmap_t*MapFromId.hmap_t*int.
Definition max_id:int := 1000000000000000000.

Definition id_alloc_make(len:int):id_alloc_t := (MapToId.hmap_make len,MapFromId.hmap_make len,0%uint63).

Definition get_key(x:int)(c:id_alloc_t):option K :=
let '(mp1,mp2,p) := c in
MapFromId.hmap_get x mp2.

Definition get_id(x:K)(c:id_alloc_t):option int :=
let '(mp1,mp2,p) := c in
MapToId.hmap_get x mp1.

Definition get_or_alloc_id(x:K)(c:id_alloc_t):option (int*id_alloc_t) :=
let '(mp1,mp2,p) := c in
match MapToId.hmap_get x mp1 with
| Some y => Some (y,c)
| None =>
  if (p <? max_id)%uint63 then
    Some (p,(MapToId.hmap_set x p mp1,MapFromId.hmap_set p x mp2,(p+1)%uint63))
  else None
end.

Definition id_alloc_WF(c:id_alloc_t):Prop :=
let '(mp1,mp2,p) := c in
MapToId.hmap_WF mp1 /\
MapFromId.hmap_WF mp2 /\
(forall x y, get_id x c = Some y <-> get_key y c = Some x) /\
(forall x,
match get_id x c with
| None => True
| Some y => (y <? p)%uint63 = true
end) /\
(0 <= φ (p)%uint63 + 1 < wB)%Z.

Lemma id_alloc_make_WF len:
id_alloc_WF (id_alloc_make len).
Proof.
  unfold id_alloc_WF,id_alloc_make.
  split.
  1: apply MapToId.hmap_make_WF.
  split.
  1: apply MapFromId.hmap_make_WF.
  unfold get_id,get_key.
  split;[|split].
  - intros x y.
    rewrite MapToId.hmap_get_make.
    rewrite MapFromId.hmap_get_make.
    split; congruence.
  - intros x.
    rewrite MapToId.hmap_get_make; trivial.
  - cbv. split; congruence.
Qed.

Lemma get_or_alloc_id_WF x c:
id_alloc_WF c ->
match get_or_alloc_id x c with
| None => True
| Some (y,c') =>
  get_id x c' = Some y /\
  id_alloc_WF c' /\
  (forall x', x'<>x -> get_id x' c' = get_id x' c)
end.
Proof.
  unfold id_alloc_WF,get_or_alloc_id.
  destruct c as [[mp1 mp2] p].
  intros [Hwf1 [Hwf2 [Hwf3 [Hwf4 Hwf5]]]].
  destruct (MapToId.hmap_get x mp1) eqn:E1.
  - split.
    1: apply E1.
    split.
    1: tauto.
    intros.
    reflexivity.
  - destruct (p <? max_id)%uint63 eqn:Ep; trivial.
    split.
    1: apply MapToId.hmap_get_set_same,Hwf1.
    split.
    + split.
      1: apply MapToId.hmap_set_WF,Hwf1.
      split.
      1: apply MapFromId.hmap_set_WF,Hwf2.
      split;[|split]. 2: {
        intros x'.
        unfold get_id.
        destruct (K_eq_spec x' x).
        - subst x'.
          rewrite MapToId.hmap_get_set_same; auto.
          rewrite ltb_spec,add_spec.
          rewrite to_Z_1.
          rewrite Z.mod_small.
          1: lia.
          apply Hwf5.
        - rewrite MapToId.hmap_get_set_other; auto.
          specialize (Hwf4 x').
          unfold get_id in Hwf4.
          destruct (MapToId.hmap_get x' mp1); trivial.
          generalize Hwf4.
          do 2 rewrite ltb_spec.
          rewrite add_spec,Z.mod_small; auto.
          rewrite to_Z_1.
          lia.
      }
      2: {
        rewrite add_spec,to_Z_1,Z.mod_small; auto.
        rewrite ltb_spec in Ep.
        eassert (φ (max_id) = _)%uint63 as E by (cbv; reflexivity).
        rewrite E in Ep; clear E.
        eassert (wB = _)%uint63 as E by (cbv; reflexivity).
        rewrite E; clear E.
        lia.
      }
      intros x' y.
      specialize (Hwf3 x' y).
      destruct (K_eq_spec x' x).
      * subst x'.
        unfold get_id,get_key.
        rewrite MapToId.hmap_get_set_same; auto.
        destruct (Uint63_K.K_eq_spec p y).
        -- subst y.
          rewrite MapFromId.hmap_get_set_same; auto.
          tauto.
        -- split.
          1: congruence.
          intro H.
          rewrite MapFromId.hmap_get_set_other in H; auto.
          unfold get_id,get_key in Hwf3.
          rewrite <-Hwf3 in H.
          congruence.
      * unfold get_id,get_key.
        unfold get_id,get_key in Hwf3.
        rewrite MapToId.hmap_get_set_other; auto.
        rewrite Hwf3.
        destruct (Uint63_K.K_eq_spec p y).
        -- subst y.
          rewrite MapFromId.hmap_get_set_same; auto.
          rewrite <-Hwf3.
          specialize (Hwf4 x').
          unfold get_id in Hwf4.
          split. 2: congruence.
          intros H.
          rewrite H,ltb_spec in Hwf4.
          lia.
        -- rewrite MapFromId.hmap_get_set_other; auto.
          tauto.
    + intros x' Hne.
      unfold get_id.
      apply MapToId.hmap_get_set_other; tauto.
Qed.

End IdAlloc.


Module HashMultimap(K_t:HashableType)(V_t:ValueType).

Module list_V_t <: ValueType.
Definition V := list V_t.V.
End list_V_t.

Module list_V_HashMap := HashMap K_t list_V_t.
Export K_t.
Export V_t.

Definition hmap_t := list_V_HashMap.hmap_t.

Definition hmap_make(len:int):hmap_t :=
list_V_HashMap.hmap_make len.

Definition hmap_get(x:K)(c:hmap_t):list V :=
match list_V_HashMap.hmap_get x c with
| Some ls => ls
| None => nil
end.

Definition hmap_add(x:K)(y:V)(c:hmap_t):hmap_t :=
list_V_HashMap.hmap_upd x (fun ls =>
y::match ls with
| None => nil
| Some ls0 => ls0
end) c.

Definition hmap_WF(c:hmap_t):Prop :=
list_V_HashMap.hmap_WF c.

Lemma hmap_make_WF len:
  hmap_WF (hmap_make len).
Proof.
  apply list_V_HashMap.hmap_make_WF.
Qed.

Lemma hmap_get_make x' len:
hmap_get x' (hmap_make len) = nil.
Proof.
  unfold hmap_get,hmap_make.
  rewrite list_V_HashMap.hmap_get_make.
  reflexivity.
Qed.

Lemma hmap_add_WF x y c:
hmap_WF c ->
hmap_WF (hmap_add x y c).
Proof.
  unfold hmap_WF,hmap_add.
  rewrite list_V_HashMap.hmap_upd_spec.
  apply list_V_HashMap.hmap_set_WF.
Qed.

Lemma hmap_get_add_same x y c:
hmap_WF c ->
hmap_get x (hmap_add x y c) = y::(hmap_get x c).
Proof.
  unfold hmap_WF,hmap_get,hmap_add.
  intro Hwf.
  rewrite list_V_HashMap.hmap_upd_spec.
  rewrite list_V_HashMap.hmap_get_set_same; auto.
Qed.

Lemma hmap_get_add_other x y c x':
hmap_WF c ->
x'<> x ->
hmap_get x' (hmap_add x y c) = (hmap_get x' c).
Proof.
  unfold hmap_WF,hmap_get,hmap_add.
  intros Hwf Hne.
  rewrite list_V_HashMap.hmap_upd_spec.
  rewrite list_V_HashMap.hmap_get_set_other; auto.
Qed.

Lemma hmap_get_add_mono x y c x' x'':
hmap_WF c ->
In x'' (hmap_get x' c) ->
In x'' (hmap_get x' (hmap_add x y c)).
Proof.
  intros Hwf Hin.
  destruct (K_eq_spec x' x).
  - subst.
    rewrite hmap_get_add_same; auto.
    right; auto.
  - rewrite hmap_get_add_other; auto.
Qed.

End HashMultimap.













