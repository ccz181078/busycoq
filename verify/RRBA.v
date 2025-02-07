Require Import ZArith.
Require Import List.
Require Import Lia.
Require Sint63.
From BusyCoq Require Import HashTable.
From BusyCoq Require TM.
From BusyCoq Require Import Eqb.
From Coq Require Import Lists.Streams.
From Coq Require Import Lists.List.
From Coq Require PArray.

Ltac destruct_spec_expr e f :=
match e with
| match ?a with _ => _ end => destruct_spec_expr a f
| if ?a then _ else _ => destruct_spec_expr a f
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 ?arg6 ?arg7 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5 arg6 arg7);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 ?arg6 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5 arg6);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 ?arg5 =>
  pose proof (f arg1 arg2 arg3 arg4 arg5);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 ?arg4 =>
  pose proof (f arg1 arg2 arg3 arg4);
  destruct e
| ?a ?arg1 ?arg2 ?arg3 =>
  pose proof (f arg1 arg2 arg3);
  destruct e
| ?a ?arg1 ?arg2 =>
  pose proof (f arg1 arg2);
  destruct e
| ?a ?arg1 =>
  pose proof (f arg1);
  destruct e
end.

Ltac destruct_spec f :=
match goal with
|- ?a => destruct_spec_expr a f
end.

Ltac simpl_Forall :=
  repeat (
  rewrite Forall_nil_iff in * ||
  rewrite Forall_cons_iff in * ||
  rewrite Forall_app in *).

Ltac simpl_N_add_mul :=
  repeat rewrite N.mul_1_l in *;
  repeat rewrite N.mul_1_r in *;
  repeat rewrite N.mul_0_l in *;
  repeat rewrite N.mul_0_r in *;
  repeat rewrite N.add_0_l in *;
  repeat rewrite N.add_0_r in *.

Definition MAXT:nat := 1000000.

Notation "a ||| b" := (match a with Some a0 => Some a0 | None => b end) (at level 40).

Definition o2b{T}(x:option T):bool :=
  if x then true else false.

Definition b2o(x:bool):option unit :=
  if x then Some tt else None.


Definition is_None{T}(x:option T):bool :=
match x with
| None => true
| _ => false
end.

Module Uint.
Import Uint63.
Open Scope uint63.

Fixpoint to_Pos_rec(x:int)(n:nat) :=
if x =? 0x1 then xH else
match n with
| O => xH
| S n0 =>
  let y := (to_Pos_rec (x>>0x1) n0) in
  (if is_even x then y~0 else y~1)%positive
end.

Definition to_N(x:int) :=
if x=?0x0 then N0 else Npos (to_Pos_rec x size).

End Uint.

Import Uint.

Import TM.

Module RRBA(Ctx:Ctx).
Module TM := TM Ctx.
Export TM.

Notation int := PrimInt63.int.
Definition neg1:int := Eval compute in Uint63.of_Z (-1).
Definition int0:int := Eval compute in Uint63.of_Z 0.
Definition int1:int := Eval compute in Uint63.of_Z 1.
Definition int2:int := Eval compute in Uint63.of_Z 2.
Definition int3:int := Eval compute in Uint63.of_Z 3.
Definition int4:int := Eval compute in Uint63.of_Z 4.
Instance int_eqb: Eqb int := {| eqb := PrimInt63.eqb; eqb_spec := Uint63_K.K_eq_spec |}.

Notation "a + b" := (PrimInt63.add a b).
Notation "a - b" := (PrimInt63.sub a b).
Notation "a * b" := (PrimInt63.mul a b).
Notation "a / b" := (PrimInt63.div a b).
Notation "a 'mod' b" := (PrimInt63.mod a b).
Notation "a <? b" := (PrimInt63.ltsb a b).


Class Sub T := {
  sub: T->T->option T;
  mul: T->Z->T;
}.

Instance ZSub: Sub Z := {|
  sub := fun a b => Some (Z.sub a b);
  mul := fun a b => (a*b)%Z;
|}.

Instance IntSub: Sub int := {|
  sub := fun a b => Some (PrimInt63.sub a b);
  mul := fun a b => (PrimInt63.mul a (Uint63.of_Z b));
|}.

Instance ListSub {A} (A_sub:Sub A): Sub (list A) := {|
  sub := fix list_sub(a b:list A):option (list A) :=
  match a,b with
  | a0::a1,b0::b1 =>
    (sub a0 b0) &&& (fun v0 =>
    (list_sub a1 b1) &&& (fun v1 =>
    Some (v0::v1)))
  | nil,nil => Some nil
  | _,_ => None
  end;
  mul := fun a b => map (fun x => mul x b) a;
|}.

Instance ProdSub {A B} (a:Sub A)(b:Sub B): Sub (A*B) := {|
  sub := fun '(a1,b1) '(a2,b2) =>
  sub a1 a2 &&& (fun a =>
  sub b1 b2 &&& (fun b =>
  Some (a,b)));
  mul := fun '(a1,a2) b =>
  (mul a1 b,mul a2 b);
|}.

Instance SumSub {A B} (a:Sub A)(b:Sub B): Sub (A+B) := {|
  sub := fun a b =>
  match a,b with
  | inl a0,inl b0 =>
    (sub a0 b0) &&& (fun v => Some (inl v))
  | inr a0,inr b0 =>
    (sub a0 b0) &&& (fun v => Some (inr v))
  | _,_ => None
  end;
  mul := fun a b =>
  match a with
  | inl a0 => inl (mul a0 b)
  | inr a0 => inr (mul a0 b)
  end;
|}.

Instance OptionSub {A} (a:Sub A): Sub (option A) := {|
  sub := fun x y =>
  match x,y with
  | Some x0,Some y0 =>
    (sub x0 y0) &&& (fun v => Some (Some v))
  | _,_ => None
  end;
  mul := fun a b =>
  match a with
  | Some a0 => Some (mul a0 b)
  | None => None
  end;
|}.

Inductive Box(T:Type) :=
| box(x:T)
.
Arguments box {T} x.

Instance BoxSub {A} (e:Eqb A): Sub (Box A) := {|
  sub := fun a b =>
  match a,b with
  | box a0,box b0 =>
    if eqb a0 b0 then Some (box a0) else None
  end;
  mul := fun a b => a;
|}.

Definition Box_eqb {A} (A_eqb:A->A->bool)(x y:Box A): bool :=
match x,y with
| box x0,box y0 =>
  A_eqb x0 y0
end.

Instance BoxEqb {A} (e:Eqb A): Eqb (Box A).
Proof.
  unshelve esplit.
  - apply Box_eqb; apply eqb.
  - intros.
    destruct x,y.
    unfold Box_eqb.
    destruct (eqb_spec x x0);
    solve_Bool_reflect.
Defined.


Notation seg := (list Sym).

Notation seg1 := (list (seg*nat)).
Notation seg1x := (list seg).
Notation seg1y := (list Z).
Notation seg2 := (list (seg*(N*N*N))).

Module Seg1xHash <: HashableType.
Import HashConcat.
Definition K := seg1x.
Definition K_eq := @eqb K _.
Definition K_eq_spec := @eqb_spec K _.
Definition K_hash := @hash K _.
End Seg1xHash.

Module Seg1xIdAlloc := IdAlloc Seg1xHash.

Section seg1_ctx.
Hypothesis max_bsz:nat.

Definition seg1_entry_to_seg(x:seg*nat):seg :=
  let (a,n):=x in
  a^^n.

Fixpoint check_rep2(x1 x2:seg1)(n:nat):bool :=
match n with
| O => true
| S n0 =>
  match x1,x2 with
  | h1::t1,h2::t2 => eqb h1 h2 && check_rep2 t1 t2 n0
  | _,_ => false
  end
end.

Fixpoint match_seg(x1 x2:seg):option seg :=
match x1 with
| nil => Some x2
| h1::t1 =>
  match x2 with
  | nil => None
  | h2::t2 => if eqb h1 h2 then match_seg t1 t2 else None
  end
end.

Fixpoint match_seg_rep(x1 x2:seg)(n:nat):option seg :=
match n with
| O => Some x2
| S n0 =>
  match_seg x1 x2 &&& (fun x2' => match_seg_rep x1 x2' n0)
end.

Fixpoint check_repS(x1:seg1)(x2:seg)(n:nat):bool :=
match n with
| O =>
  match x2 with
  | nil => true
  | _ => false
  end
| S n0 =>
  match x1 with
  | (h1,n1)::t1 =>
    match match_seg_rep h1 x2 n1 with
    | None => false
    | Some x2' => check_repS t1 x2' n0
    end
  | _ => false
  end
end.

Definition find_rep2 x1 x2 n :=
if check_rep2 x1 x2 n then
  let w := flat_map seg1_entry_to_seg (firstn n x2) in
  if Nat.leb (length w) max_bsz then
    Some ((w,2)::(skipn n x2))
  else None
else None.

Definition find_repS x1 x2 n :=
(match x2 with
| (h2,n2)::t2 =>
  if check_repS x1 h2 n && Nat.leb (length h2) max_bsz then
    Some ((h2,S n2)::t2)
  else None
| _ => None
end)%bool.


Fixpoint simpl_seg1_0(x1 x2:seg1)(n:nat):option seg1 :=
find_rep2 x1 x2 n |||
find_repS x1 x2 n |||
match x2 with
| _::t2 => simpl_seg1_0 x1 t2 (S n)
| nil => None
end.

Definition simpl_seg1_1 x1 :=
match x1 with
| nil => None
| _::x2 => simpl_seg1_0 x1 x2 1
end.

Fixpoint simpl_seg1_2 x n :=
match n with
| O => x
| S n0 =>
  match simpl_seg1_1 x with
  | Some x' => simpl_seg1_2 x' n0
  | None => x
  end
end.

Definition max_simpl_depth:nat := 64.

Definition simpl_seg1(x:seg1):seg1 :=
  simpl_seg1_2 x max_simpl_depth.

Fixpoint to_seg1(x:seg):seg1 :=
match x with
| nil => nil
| x0::x1 =>
  simpl_seg1 (([x0],1)::(to_seg1 x1))
end.

Definition to_seg1xy(x:seg):seg1x*seg1y :=
let x0 := to_seg1 x in
(map fst x0,
map (fun x => Z.of_nat (snd x)) x0).

Definition seg_to_id_args(x:seg)(id:Seg1xIdAlloc.id_alloc_t):option (int*seg1y*Seg1xIdAlloc.id_alloc_t) :=
let (a,b) := to_seg1xy x in
Seg1xIdAlloc.get_or_alloc_id a id &&& (fun '(a,id) => Some (a,b,id)).

End seg1_ctx.

Module Config0.
Import HashConcat.

Definition T:Type := seg*seg*Q*dir.

Definition T0:T := ([],[],q0,R).

Definition to_config (x:T) (l0 r0:side) :=
let '(l,r,s,sgn):=x in
match sgn with
| L => l0 <* r <{{s}} l *> r0
| R => l0 <* l {{s}}> r *> r0
end.

Definition to_config' (x:T) :=
let '(l,r,s,sgn):=x in
match sgn with
| L => const s0 <* r <{{s}} l *> const s0
| R => const s0 <* l {{s}}> r *> const s0
end.

Fixpoint match_side(a b:seg):option (seg*seg) :=
match a,b with
| a0::a1,b0::b1 => if eqb a0 b0 then match_side a1 b1 else None
| _,_ => Some (a,b)
end.

Definition match_(x y:T):option (seg*seg*seg*seg) :=
let '(l1,r1,s1,sgn1):=x in
let '(l2,r2,s2,sgn2):=y in
if ((eqb s1 s2) && (eqb sgn1 sgn2))%bool then
match_side l1 l2 &&& (fun '(l2',l1') =>
match_side r1 r2 &&& (fun '(r2',r1') =>
Some (l1',r1',l2',r2')
))
else None.

Definition Tx:Type := int*int*Q*dir.
Definition Ty:Type := seg1y*seg1y.

Definition to_id_args cfg (x:T) id: option (Tx*Ty*_) :=
let '(l1,r1,s1,sgn1):=x in
seg_to_id_args cfg l1 id &&& (fun '(l1x,l1y,id) =>
seg_to_id_args cfg r1 id &&& (fun '(r1x,r1y,id) =>
Some ((l1x,r1x,s1,sgn1),(l1y,r1y),id)
)).


End Config0.

Module Rule0.
Import Config0.
Definition T:Type := Config0.T*Config0.T.

Definition to_prop (x:T)(tm:TM) :=
let (x1,x2):=x in
forall l r,
to_config x1 l r -[ tm ]->*
to_config x2 l r.

Definition subst1(x:T)(l r:list Sym):T :=
let (x1,x2):=x in
let '(l1,r1,s1,sgn1):=x1 in
let '(l2,r2,s2,sgn2):=x2 in
let (l',r'):=(if eqb sgn1 sgn2 then (l,r) else (r,l)) in
(
(l1++l,r1++r,s1,sgn1),
(l2++l',r2++r',s2,sgn2)
).

Definition subst2(x:T)(l r:list Sym):T :=
let (x1,x2):=x in
let '(l1,r1,s1,sgn1):=x1 in
let '(l2,r2,s2,sgn2):=x2 in
let (l',r'):=(if eqb sgn1 sgn2 then (l,r) else (r,l)) in
(
(l1++l',r1++r',s1,sgn1),
(l2++l,r2++r,s2,sgn2)
).

Lemma subst1_spec x l r tm:
  to_prop x tm ->
  to_prop (subst1 x l r) tm.
Proof.
  destruct x as [x1 x2].
  destruct x1 as [[[l1 r1] s1] sgn1].
  destruct x2 as [[[l2 r2] s2] sgn2].
  destruct sgn1,sgn2; cbn; intros.
  all: repeat rewrite Str_app_assoc.
  all: apply H.
Qed.

Lemma subst2_spec x l r tm:
  to_prop x tm ->
  to_prop (subst2 x l r) tm.
Proof.
  destruct x as [x1 x2].
  destruct x1 as [[[l1 r1] s1] sgn1].
  destruct x2 as [[[l2 r2] s2] sgn2].
  destruct sgn1,sgn2; cbn; intros.
  all: repeat rewrite Str_app_assoc.
  all: apply H.
Qed.

Definition follow_rule(x y:T):option (T*(seg*seg*seg*seg)) :=
match_ (snd x) (fst y) &&& (fun w =>
let '(l1,r1,l2,r2) := w in
let x':=subst2 x l1 r1 in
let y':=subst1 y l2 r2 in
if eqb (snd x') (fst y') then
Some (fst x',snd y',w)
else None
).

Lemma follow_rule_spec x y tm:
match follow_rule x y with
| None => True
| Some (z,_) =>
  to_prop x tm ->
  to_prop y tm ->
  to_prop z tm
end.
Proof.
  destruct x as [x1 x2].
  destruct y as [y1 y2].
  unfold follow_rule.
  cbn[snd]. cbn[fst].
  unfold if_Some.
  destruct_spec match_; trivial.
  destruct p as [[[l1 r1] l2] r2].
  destruct (eqb_spec (snd (subst2 (x1, x2) l1 r1)) (fst (subst1 (y1, y2) l2 r2))); trivial.
  intros Hx Hy.
  epose proof (subst2_spec _ l1 r1 _ Hx) as Hx'.
  epose proof (subst1_spec _ l2 r2 _ Hy) as Hy'.
  destruct (subst2 (x1,x2) l1 r1) as [x1' x2'].
  destruct (subst1 (y1,y2) l2 r2) as [y1' y2'].
  cbn.
  intros.
  cbn in e.
  inverts e.
  eapply evstep_trans; eauto.
Qed.

Definition step1_rule s0 i0 sgn0 tm: option T :=
  tm (s0,i0) &&& (fun '(o1,sgn1,s1) =>
  Some (([],[i0],s0,sgn0),([o1],[],s1,sgn1))
  ).

Lemma step1_rule_spec s0 i0 sgn0 tm:
match step1_rule s0 i0 sgn0 tm with
| Some x => to_prop x tm
| None => True
end.
Proof.
  unfold step1_rule,if_Some.
  destruct (tm (s0,i0)) as [[[o1 sgn1] s1]|] eqn:E; trivial.
  cbn.
  intros.
  destruct sgn0,sgn1; cbn.
  all: eapply progress_evstep; eauto.
Qed.

Definition step0_rule(x:Config0.T):T := (x,x).

Lemma step0_rule_spec x tm:
to_prop (step0_rule x) tm.
Proof.
  destruct x as [[[l1 r1] s1] sgn1].
  cbn.
  intros.
  destruct sgn1; cbn; eauto.
Qed.
(*
Definition Tx':Type := Tx*Tx*(int*int*int*int).
Definition Ty':Type := Ty*Ty*(seg1y*seg1y*seg1y*seg1y).
Definition to_id_args cfg (x:T*(seg*seg*seg*seg)) id: option ((Box Tx')*Ty'*_) :=
let '(x1,x2,(v1,v2,v3,v4)):=x in
Config0.to_id_args cfg x1 id &&& (fun '(x1x,x1y,id) =>
Config0.to_id_args cfg x2 id &&& (fun '(x2x,x2y,id) =>
seg_to_id_args cfg v1 id &&& (fun '(v1x,v1y,id) =>
seg_to_id_args cfg v2 id &&& (fun '(v2x,v2y,id) =>
seg_to_id_args cfg v3 id &&& (fun '(v3x,v3y,id) =>
seg_to_id_args cfg v4 id &&& (fun '(v4x,v4y,id) =>
Some (box (x1x,x2x,(v1x,v2x,v3x,v4x)),(x1y,x2y,(v1y,v2y,v3y,v4y)),id)
)))))).

Definition info_t:Type :=
  ((Box Tx')*Ty'*(int*int)).
 *)
Definition info_t:Type :=
  (T*(seg*seg*seg*seg)*(int*int)).
End Rule0.

Module Rule0Hash <: HashableType.
Import HashConcat.
Import Config0.
Definition K := Rule0.T.
Definition K_eq := @eqb K _.
Definition K_eq_spec := @eqb_spec K _.
Definition K_hash := @hash K _.
End Rule0Hash.

Module Rule0IdAlloc := IdAlloc Rule0Hash.

Module Config0Hash <: HashableType.
Import HashConcat.
Import Config0.
Definition K := Config0.T.
Definition K_eq := @eqb K _.
Definition K_eq_spec := @eqb_spec K _.
Definition K_hash := @hash K _.
End Config0Hash.

Module Rule0Value <: ValueType.
Definition V:Type :=Rule0.T.
End Rule0Value.

Module Mem := HashMap Config0Hash Rule0Value.

Notation config2 := (seg2*seg2*Q*dir)%type.
Notation N3 := (N*N*N)%type.
Notation N3_0 := (0,0,0)%N.
Notation N3_1 := (0,0,1)%N.
Notation rule2 := (config2*config2*N3*(N*N+N))%type.
Notation rule3 := ((list (config2*config2))*N3*N)%type.
Notation rule2ls := (list rule2)%type.
Notation rule4 := (list (rule2ls*rule2ls))%type.

Definition N3add(a b:N3) :=
let '(a0,a1,a2):=a in
let '(b0,b1,b2):=b in
(a0+b0,a1+b1,a2+b2)%N.

Definition N3mul(a:N3)(b:N) :=
let '(a0,a1,a2):=a in
(a0*b,a1*b,a2*b)%N.

Definition N3dot(a b:N3) :=
let '(a0,a1,a2):=a in
let '(b0,b1,b2):=b in
(a0*b0+a1*b1+a2*b2)%N.


Section seg2_ctx.

Section csubst_ctx.
Hypothesis i0 i1:N.

Definition seg2_entry_csubst(a:seg*N3):seg :=
let '(x,(y0,y1,y)) := a in
x^^(N.to_nat (y0*i0+y1*i1+y)).

Fixpoint seg2_csubst(x:seg2):seg :=
match x with
| h::t => seg2_entry_csubst h ++ seg2_csubst t
| [] => []
end.

Definition config2_csubst(x:config2):Config0.T :=
let '(l,r,s,sgn):=x in
(seg2_csubst l,seg2_csubst r,s,sgn).

Lemma seg2_csubst_app a b:
  seg2_csubst (a++b) = seg2_csubst a ++ seg2_csubst b.
Proof.
  induction a; trivial.
  cbn.
  rewrite IHa.
  rewrite app_assoc.
  reflexivity.
Qed.

End csubst_ctx.

Definition rule2_to_pred(tm:TM)(c:N)(x:rule2)(i0 i1:N):Prop :=
let '(c1,c2,c3,c4):=x in
(
match c4 with
| inl (l,r) => l <= N3dot c3 (i0,i1,1) < r+c
| inr v => N3dot c3 (i0,i1,1)%N = v+c
end
)%N ->
Rule0.to_prop (config2_csubst i0 i1 c1,config2_csubst i0 i1 c2) tm.

Definition rule2_to_prop tm c x:Prop :=
  forall i0 i1, rule2_to_pred tm c x i0 i1.

Definition rule3_to_pred_0 tm c12 i0 i1:Prop :=
(Forall (fun '(c1,c2) => Rule0.to_prop (config2_csubst i0 i1 c1,config2_csubst i0 i1 c2) tm) c12)%N.

Definition rule3_to_pred tm c x i0 i1:Prop :=
(let '(c12,c3,c4):=x in
N3dot c3 (i0,i1,1)%N = c4+c ->
rule3_to_pred_0 tm c12 i0 i1)%N.

Section subst_ctx.
Hypothesis i0 i1:N3.

Definition N3_subst(a:N3):N3 :=
let '(y0,y1,y):=a in
(N3add (N3add (N3mul i0 y0) (N3mul i1 y1)) (N3mul N3_1 y)).

Definition seg2_entry_subst(a:seg*N3):seg*N3 :=
let '(x,y) := a in
(x,N3_subst y).

Definition seg2_subst(x:seg2):seg2 :=
map seg2_entry_subst x.

Definition config2_subst(x:config2):config2 :=
let '(l,r,s,sgn):=x in
(seg2_subst l,seg2_subst r,s,sgn).

Definition rule2_subst_simpl(x:rule2):rule2 :=
let '(c1,c2,(c30,c3),c4):=x in
match c4 with
| inl (l,r) =>
  let d := N.min r c3 in
  (c1,c2,(c30,c3-d),inl (l-d,r-d))%N
| inr r =>
  let d := N.min r c3 in
  (c1,c2,(c30,c3-d),inr (r-d))%N
end.

Definition rule2_subst(x:rule2):rule2 :=
let '(c1,c2,c3,c4):=x in
rule2_subst_simpl (config2_subst c1,config2_subst c2,N3_subst c3,c4).

Definition rule3_subst_simpl(x:rule3):rule3 :=
let '(c12,(c30,c3),c4):=x in
let d := N.min c4 c3 in
(c12,(c30,c3-d),c4-d)%N.

Definition rule3_subst(x:rule3):rule3 :=
let '(c12,c3,c4):=x in
rule3_subst_simpl (map (fun '(c1,c2) => (config2_subst c1,config2_subst c2)) c12,N3_subst c3,c4).

End subst_ctx.

Lemma seg2_subst_spec i0' i1' x i0 i1:
  (seg2_csubst i0 i1 (seg2_subst i0' i1' x) =
  seg2_csubst (N3dot i0' (i0,i1,1)) (N3dot i1' (i0,i1,1)) x)%N.
Proof.
  induction x; trivial.
  cbn.
  rewrite <-IHx.
  f_equal.
  destruct i0' as [[a1 a2] a3].
  destruct i1' as [[b1 b2] b3].
  destruct a as [v0 [[y0 y1] y]].
  cbn - [N.mul].
  f_equal. lia.
Qed.

Lemma config2_subst_spec i0' i1' x i0 i1:
  (config2_csubst i0 i1 (config2_subst i0' i1' x) =
  config2_csubst (N3dot i0' (i0,i1,1)) (N3dot i1' (i0,i1,1)) x)%N.
Proof.
  destruct x as [[[l r] s] sgn].
  cbn.
  repeat rewrite seg2_subst_spec.
  reflexivity.
Qed.

Lemma rule2_subst_simpl_spec tm C x i0 i1:
  (rule2_to_pred tm C (rule2_subst_simpl x) i0 i1 <->
  rule2_to_pred tm C x i0 i1)%N.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c3 as [[y0 y1] y].
  destruct c4 as [[l r]|r];
  cbn;
  split; intros H H0; apply H; lia.
Qed.

Lemma rule2_subst_spec tm C i0' i1' x i0 i1:
  (rule2_to_pred tm C (rule2_subst i0' i1' x) i0 i1 <->
  rule2_to_pred tm C x (N3dot i0' (i0,i1,1)) (N3dot i1' (i0,i1,1)))%N.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  unfold rule2_subst.
  rewrite rule2_subst_simpl_spec.
  destruct c3 as [[y0 y1] y].
  destruct i0' as [[a1 a2] a3].
  destruct i1' as [[b1 b2] b3].
  cbn - [N.mul].
  repeat rewrite config2_subst_spec.
  cbn - [N.mul].
  split; intros H H0; apply H;
  destruct c4 as [[l r]|r]; lia.
Qed.

Lemma rule3_subst_simpl_spec tm C x i0 i1:
  (rule3_to_pred tm C (rule3_subst_simpl x) i0 i1 <->
  rule3_to_pred tm C x i0 i1)%N.
Proof.
  destruct x as [[c12 c3] c4].
  destruct c3 as [[y0 y1] y].
  cbn;
  split; intros H H0; apply H; lia.
Qed.

Definition rule3_to_list_rule2(x:rule3):list rule2 :=
let '(c12,c3,c4):=x in
map (fun a => (a,c3,inr c4)) c12.

Definition rule3_from_list_rule2'(x:list rule2):option rule3 :=
hd_error x &&& (fun '(_,c3,c4) =>
match c4 with
| inr c4 =>
  Some (map (fun '(c12,c3,c4) => c12) x,c3,c4)
| _ => None
end).

Definition rule3_from_list_rule2(x:list rule2):option rule3 :=
  rule3_from_list_rule2' x &&& (fun v =>
  if eqb (rule3_to_list_rule2 v) x then Some v else None).

Lemma rule3_to_list_rule2_spec tm C x i0 i1:
  rule3_to_pred tm C x i0 i1 <->
  Forall (fun x => rule2_to_pred tm C x i0 i1) (rule3_to_list_rule2 x).
Proof.
  destruct x as [[c12 c3] c4].
  induction c12 as [|[c1 c2] c12].
  - cbn.
    unfold rule3_to_pred_0.
    cbn.
    simpl_Forall.
    tauto.
  - cbn.
    unfold rule3_to_pred_0.
    cbn.
    simpl_Forall.
    rewrite <-IHc12.
    unfold rule2_to_pred,rule3_to_pred.
    tauto.
Qed.

Lemma rule3_from_list_rule2_spec tm C x i0 i1:
match rule3_from_list_rule2 x with
| Some v =>
  rule3_to_pred tm C v i0 i1 <->
  Forall (fun x => rule2_to_pred tm C x i0 i1) (x)
| None => True
end.
Proof.
  unfold rule3_from_list_rule2.
  unfold if_Some.
  destruct (rule3_from_list_rule2' x) as [a0|]; trivial.
  destruct_spec (@eqb_spec (list rule2)); trivial.
  inverts H.
  apply rule3_to_list_rule2_spec.
Qed.

Lemma rule3_subst_spec tm C i0' i1' x i0 i1:
  (rule3_to_pred tm C (rule3_subst i0' i1' x) i0 i1 <->
  rule3_to_pred tm C x (N3dot i0' (i0,i1,1)) (N3dot i1' (i0,i1,1)))%N.
Proof.
  repeat rewrite rule3_to_list_rule2_spec.
  destruct x as [[c12 c3] c4].
  induction c12 as [|[c1 c2] c12].
  - cbn.
    destruct (N3_subst i0' i1' c3) as [c30 c31].
    cbn.
    simpl_Forall.
    tauto.
  - cbn.
    simpl_Forall.
    rewrite <-IHc12.
    destruct (N3_subst i0' i1' c3) as [c30 c31] eqn:E.
    unfold rule3_to_list_rule2.
    cbn.
    simpl_Forall.
    rewrite E.
    epose proof (rule2_subst_spec tm C i0' i1' (c1,c2,c3,inr c4) i0 i1).
    cbn in H.
    rewrite E in H.
    rewrite <-H.
    tauto.
Qed.

Definition rule2_i0_O_S(x:rule2):rule2*rule2 :=
  (
  (rule2_subst (0,0,0) (0,1,0) x),
  (rule2_subst (1,0,1) (0,1,0) x)
  )%N.

Definition rule2_i1_O_S(x:rule2):rule2*rule2 :=
  (
  (rule2_subst (1,0,0) (0,0,0) x),
  (rule2_subst (1,0,0) (0,1,1) x)
  )%N.

Definition rule2_lt_r_S(x:rule2):option (rule2*rule2) :=
let '(c123,c4):=x in
match c4 with
| inl (l,r) =>
  Some (
  (c123,inr (r-1)),
  (c123,inl (l,r-1))
  )%N
| _ => None
end.

Definition rule2_lt_to_eq(x:rule2)(n:N):option rule2 :=
let '(c123,c4):=x in
match c4 with
| inl (l,r) =>
  let v:=(r-1-n)%N in
  if ((l<=?v)%N && (v<?r)%N)%bool then
  Some (c123,inr v)
  else None
| _ => None
end.

Definition rule2_lt_to_eq'(x:rule2):option rule2 :=
let '(c12,c3,c4):=x in
match c4 with
| inl (l,Npos r) =>
  if eqb (c3,l) (1,0,0,0)%N then
    Some (c12,(1,1,0),inr (Pos.pred_N r))%N
  else None
| _ => None
end.


Definition rule2_lt_l_simpl(x:rule2):rule2 :=
let '(c12,c3,c4):=x in
match c4 with
| inl (l,r) =>
  if eqb c3 (1,0,0)%N then
  rule2_subst (1,0,l)%N N3_0 x
  else x
| _ => x
end.

Definition rule2_eq_r_simpl(x:rule2):rule2 :=
let '(c12,c3,c4):=x in
match c4 with
| inr r =>
  if eqb c3 (1,0,0)%N then
  rule2_subst (1,0,r)%N (0,1,0)%N x
  else x
| _ => x
end.

Fixpoint rule2_i0_O_S_n(x:rule2)(n:nat):(list rule2)*rule2 :=
match n with
| O => ([],x)
| S n =>
  let '(x0,x1):=rule2_i0_O_S_n x n in
  let '(x2,x3):=rule2_i0_O_S x1 in
  (x2::x0,x3)
end.

Fixpoint rule2_i1_O_S_n(x:rule2)(n:nat):(list rule2)*rule2 :=
match n with
| O => ([],x)
| S n =>
  let '(x0,x1):=rule2_i1_O_S_n x n in
  let '(x2,x3):=rule2_i1_O_S x1 in
  (x2::x0,x3)
end.


Lemma rule2_i0_O_S_spec tm C x:
  (rule2_to_prop tm C (rule2_subst (0,0,0) (0,1,0) x) ->
  rule2_to_prop tm C (rule2_subst (1,0,1) (0,1,0) x) ->
  rule2_to_prop tm C x)%N.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c3 as [[y0 y1] y].
  intros HO HS i0 i1 H.
  destruct i0 as [|i0].
  - specialize (HO N0 i1).
    rewrite rule2_subst_spec in HO.
    cbn - [N.mul] in HO.
    cbn in H.
    cbn.
    intros l0 r0.
    applys_eq HO.
    1,2: repeat (lia || f_equal).
    destruct c4 as [[l r]|r]; lia.
  - specialize (HS (Pos.pred_N i0) i1)%N.
    rewrite rule2_subst_spec in HS.
    cbn - [N.mul] in HS.
    cbn in H.
    cbn.
    intros l0 r0.
    applys_eq HS.
    1,2: repeat (lia || f_equal).
    destruct c4 as [[l r]|r]; lia.
Qed.

Lemma rule2_i1_O_S_spec tm C x:
  (rule2_to_prop tm C (rule2_subst (1,0,0) (0,0,0) x) ->
  rule2_to_prop tm C (rule2_subst (1,0,0) (0,1,1) x) ->
  rule2_to_prop tm C x)%N.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c3 as [[y0 y1] y].
  intros HO HS i0 i1 H.
  destruct i1 as [|i1].
  - specialize (HO i0 N0).
    rewrite rule2_subst_spec in HO.
    cbn - [N.mul] in HO.
    cbn in H.
    cbn.
    intros l0 r0.
    applys_eq HO.
    1,2: repeat (lia || f_equal).
    destruct c4 as [[l r]|r]; lia.
  - specialize (HS i0 (Pos.pred_N i1))%N.
    rewrite rule2_subst_spec in HS.
    cbn - [N.mul] in HS.
    cbn in H.
    cbn.
    intros l0 r0.
    applys_eq HS.
    1,2: repeat (lia || f_equal).
    destruct c4 as [[l r]|r]; lia.
Qed.

Lemma rule2_i0_O_S_n_spec tm C x n:
  let '(x0,x1):=rule2_i0_O_S_n x n in
  Forall (rule2_to_prop tm C) x0 ->
  rule2_to_prop tm C x1 ->
  rule2_to_prop tm C x.
Proof.
  induction n.
  1: cbn; tauto.
  cbn.
  destruct_spec rule2_i0_O_S_n.
  simpl_Forall.
  intros.
  apply IHn; try tauto.
  apply rule2_i0_O_S_spec; tauto.
Qed.

Lemma rule2_i1_O_S_n_spec tm C x n:
  let '(x0,x1):=rule2_i1_O_S_n x n in
  Forall (rule2_to_prop tm C) x0 ->
  rule2_to_prop tm C x1 ->
  rule2_to_prop tm C x.
Proof.
  induction n.
  1: cbn; tauto.
  cbn.
  destruct_spec rule2_i1_O_S_n.
  simpl_Forall.
  intros.
  apply IHn; try tauto.
  apply rule2_i1_O_S_spec; tauto.
Qed.

Lemma rule2_lt_r_S_spec x:
match rule2_lt_r_S x with
| None => True
| Some (x0,x1) =>
  forall tm C,
  rule2_to_prop tm C x0 ->
  rule2_to_prop tm C x1 ->
  rule2_to_prop tm C x
end.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c4 as [[l r]|r].
  2: cbn; trivial.
  cbn; intros tm C.
  unfold rule2_to_prop.
  cbn.
  intros HO HS i0 i1 H l0 r0.
  cbn.
  specialize (HO i0 i1).
  specialize (HS i0 i1).
  remember (N3dot c3 (i0,i1,1%N)) as v1.
  assert (v1=r-1+C \/ l<=v1<r-1+C)%N as E by lia.
  destruct E as [E|E].
  - apply HO,E.
  - apply HS,E.
Qed.

Lemma rule2_lt_to_eq_spec x n:
match rule2_lt_to_eq x n with
| None => True
| Some (x0) =>
  forall tm C i0 i1,
  rule2_to_pred tm C x i0 i1 ->
  rule2_to_pred tm C x0 i0 i1
end.
Proof with trivial.
  destruct x as [[[c1 c2] c3] c4].
  destruct c4 as [[l r]|r]; cbn...
  destruct (N.leb_spec l (r-1-n))%N...
  destruct (N.ltb_spec (r-1-n) r)%N...
  cbn.
  intros.
  apply H1; lia.
Qed.

Lemma rule2_lt_to_eq'_spec x:
match rule2_lt_to_eq' x with
| None => True
| Some (x0) =>
  forall tm C,
  rule2_to_prop tm C x ->
  rule2_to_prop tm C x0
end.
Proof with trivial.
  destruct x as [[[c1 c2] c3] c4].
  destruct c4 as [[l r]|r]; cbn - [eqb]...
  destruct r as [|r]...
  destruct (eqb_spec (c3,l) (1,0,0,0))%N...
  intros tm C.
  inverts e.
  unfold rule2_to_prop.
  unfold rule2_to_pred.
  unfold N3dot.
  intros.
  specialize (H i0 (Pos.pred_N r + C - i0))%N.
  simpl_N_add_mul.
  applys_eq H;
  repeat (lia || f_equal).
Qed.

Lemma rule2_lt_l_simpl_spec x:
  forall tm C,
  rule2_to_prop tm C x ->
  rule2_to_prop tm C (rule2_lt_l_simpl x).
Proof with trivial.
  destruct x as [[[c1 c2] c3] c4].
  destruct c4 as [[l r]|r]...
  intros.
  unfold rule2_lt_l_simpl.
  destruct (eqb_spec c3 (1,0,0))%N...
  subst c3.
  unfold rule2_to_prop in *.
  intros i0 i1.
  rewrite rule2_subst_spec.
  specialize (H (i0+l)%N N0).
  cbn - [N.mul] in *.
  simpl_N_add_mul.
  apply H.
Qed.

Lemma rule2_eq_r_simpl_spec x:
  forall tm C,
  rule2_to_prop tm C x <->
  rule2_to_prop tm C (rule2_eq_r_simpl x).
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c4 as [[l r]|r].
  1: cbn; intros; tauto.
  intros.
  unfold rule2_eq_r_simpl.
  destruct (eqb_spec c3 (1,0,0))%N.
  2: tauto.
  subst c3.
  unfold rule2_to_prop in *.
  split;
  intros H i0 i1.
  - rewrite rule2_subst_spec in *.
    specialize (H (i0+r)%N i1).
    cbn - [N.mul] in *.
    simpl_N_add_mul.
    apply H.
  - specialize (H (i0-r)%N i1).
    rewrite rule2_subst_spec in *.
    cbn - [N.mul] in *.
    simpl_N_add_mul.
    intros H0.
    replace (i0-r+r)%N with i0 in H by lia.
    apply H,H0.
Qed.

Definition rule2_subst_Sc(x:rule2):rule2 :=
let '(c123,c4):=x in
(c123,
match c4 with
| inl (l,r) => inl (l,r+1) 
| inr r => inr (r+1)
end)%N.

Lemma rule2_subst_Sc_spec tm c x:
  rule2_to_prop tm c (rule2_subst_Sc x) <->
  rule2_to_prop tm (c+1)%N x.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c3 as [[y0 y1] y].
  cbn.
  split; intros H i0 i1 H0; apply H;
  destruct c4 as [[l r]|r]; lia.
Qed.

Fixpoint seg2_to_seg(x:seg2):option seg :=
match x with
| (x,(y0,y1,y))::t =>
  if (eqb (y0,y1) (N0,N0)) then
    seg2_to_seg t &&& (fun v' => Some ((x^^(N.to_nat y))++v'))
  else None
| _ => Some []
end.

Definition config2_to_config0(x:config2):option Config0.T :=
let '(l,r,s,sgn):=x in
seg2_to_seg l &&& (fun l =>
seg2_to_seg r &&& (fun r =>
Some (l,r,s,sgn))).

Definition rule2_to_rule0(x:rule2):option Rule0.T :=
let '(c1,c2,(a0,a1,a2),c4):=x in
config2_to_config0 c1 &&& (fun c1 =>
config2_to_config0 c2 &&& (fun c2 =>
  Some (c1,c2))).

Lemma seg2_to_seg_spec x:
match seg2_to_seg x with
| None => True
| Some x' =>
  forall i0 i1,
  x' = seg2_csubst i0 i1 x
end.
Proof.
  induction x as [|[x0 [[y0 y1] y]] x].
  - cbn; reflexivity.
  - cbn - [eqb].
    destruct (eqb_spec (y0,y1) (0,0))%N; trivial.
    inverts e.
    unfold if_Some.
    destruct (seg2_to_seg x); trivial.
    intros.
    specialize (IHx i0 i1).
    rewrite IHx.
    reflexivity.
Qed.

Lemma config2_to_config0_spec x:
match config2_to_config0 x with
| None => True
| Some x' =>
  forall i0 i1,
  x' = config2_csubst i0 i1 x
end.
Proof.
  destruct x as [[[l r] s] sgn].
  cbn.
  unfold if_Some.
  destruct_spec seg2_to_seg_spec; trivial.
  destruct_spec seg2_to_seg_spec; trivial.
  intros.
  rewrite (H i0 i1).
  rewrite (H0 i0 i1).
  reflexivity.
Qed.

Lemma rule2_to_rule0_spec tm x:
match rule2_to_rule0 x with
| None => True
| Some x' =>
  Rule0.to_prop x' tm ->
  rule2_to_prop tm N0 x
end.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c3 as [[y0 y1] y].
  cbn.
  unfold if_Some.
  destruct_spec config2_to_config0_spec; trivial.
  destruct_spec config2_to_config0_spec; trivial.
  intros Ha i0 i1 Hb.
  rewrite <-H,<-H0.
  apply Ha.
Qed.

Fixpoint rule2_to_list_rule0(T:nat)(x:rule2):option (list Rule0.T) :=
match T with
| O => None
| S T =>
  let '(c12,(a0,a1,a2),c4):=x in
  match c4 with
  | inl (l,r) =>
    if (l<?r)%N then
      rule2_lt_r_S x &&& (fun '(x0,x1) =>
      rule2_to_list_rule0 T x0 &&& (fun v1 =>
      rule2_to_list_rule0 T x1 &&& (fun v2 =>
      Some (v1++v2))))
    else
      Some []
  | inr r =>
    if (r<?a2)%N then Some [] else
    (if eqb a1 N0 then
      if eqb (a0,a2) (1,0)%N then
        rule2_to_list_rule0 T (rule2_subst (0,0,r) (0,1,0) x)
      else if eqb a0 N0 then
        rule2_to_rule0 x &&& (fun v => Some [v])
      else None
    else
      let '(x0,x1):=rule2_i1_O_S x in
      rule2_to_list_rule0 T x0 &&& (fun v1 =>
      rule2_to_list_rule0 T x1 &&& (fun v2 =>
      Some (v1++v2))))%N
  end
end.


Lemma rule2_to_list_rule0_spec tm T x:
match rule2_to_list_rule0 T x with
| Some ls =>
  Forall (fun a => Rule0.to_prop a tm) ls ->
  rule2_to_prop tm N0 x
| None => True
end.
Proof.
  gen x.
  induction T; intros x.
  1: reflexivity.
  destruct x as [[[c1 c2] c3] c4].
  destruct c3 as [[y0 y1] y].
  cbn[rule2_to_list_rule0].
  unfold if_Some.
  destruct c4 as [[l r]|r].
  - destruct (N.ltb_spec l r).
    2:{
      intros Hls i0 i1 Hlr.
      cbn in Hlr.
      lia.
    }
    destruct_spec (rule2_lt_r_S_spec); trivial.
    destruct p as [x0 x1].
    destruct_spec IHT; trivial.
    destruct_spec IHT; trivial.
    simpl_Forall.
    intros [Ha Hb].
    apply H0; tauto.
  - destruct (N.ltb_spec r y).
    1:{
      intros Hls i0 i1 Hlr.
      cbn in Hlr.
      lia.
    }
    destruct (eqb_spec y1 N0).
    + destruct (eqb_spec (y0,y) (1,0)%N).
      2:{
        destruct (eqb_spec y0 N0); trivial.
        destruct_spec (rule2_to_rule0_spec tm); trivial.
        intros Hls.
        apply H0.
        simpl_Forall.
        tauto.
      }
      inverts e.
      inverts e0.
      destruct_spec IHT; trivial.
      intros Hls i0 i1 He l0 r0.
      specialize (H0 Hls i0 i1). clear Hls.
      rewrite rule2_subst_spec in H0.
      cbn - [N.mul] in H0,He.
      applys_eq H0;
      repeat (lia || f_equal).
    + unfold rule2_i1_O_S.
      destruct_spec IHT; trivial.
      destruct_spec IHT; trivial.
      simpl_Forall.
      intros [Ha Hb].
      apply rule2_i1_O_S_spec; tauto.
Qed.

Fixpoint rule3_subst_batch_0(x:rule3)(i0' i1':N->N->N3)(T:nat)(j0 j1:N):list rule3 :=
rule3_subst (i0' j0 j1) (i1' j0 j1) x ::
match T with
| O => []
| S T => rule3_subst_batch_0 x i0' i1' T (N.pred j0) (N.succ j1)
end.

Lemma rule3_subst_batch_spec_0' x i0' i1' k0 k1:
  forall j0 j1,
  (j0+j1=k0+k1)%N ->
  (j0<=k0)%N ->
  In (rule3_subst (i0' j0 j1) (i1' j0 j1) x) (rule3_subst_batch_0 x i0' i1' (N.to_nat k0) k0 k1).
Proof.
  gen k1.
  remember (N.to_nat k0) as T.
  gen k0.
  induction T; intros.
  - cbn. left.
    repeat (lia || f_equal).
  - cbn.
    assert (j0=k0\/j0<=N.pred k0)%N as [E|E] by lia.
    + subst j0.
      left.
      repeat (lia || f_equal).
    + right.
      apply IHT; lia.
Qed.

Lemma rule3_subst_batch_spec_0'' y x i0' i1' k0 k1:
  In y (rule3_subst_batch_0 x i0' i1' (N.to_nat k0) k0 k1) ->
  exists j0 j1,
  (j0+j1=k0+k1)%N /\
  (j0<=k0)%N /\
  y = rule3_subst (i0' j0 j1) (i1' j0 j1) x.
Proof.
  gen k1.
  remember (N.to_nat k0) as T.
  gen k0.
  induction T; intros.
  - cbn.
    exists N0 k1.
    split; [lia|].
    split; [lia|].
    cbn in H.
    destruct H as [H|H]. 2: tauto.
    rewrite <-H.
    repeat (lia || f_equal).
  - cbn in H.
    destruct H as [H|H].
    + exists k0 k1.
      split; [lia|].
      split; [lia|].
      rewrite H.
      reflexivity.
    + unshelve epose proof (IHT _ _ _ H) as IHT.
      1: lia.
      destruct IHT as [j0 [j1 [I0 [I1 I2]]]].
      exists j0 j1.
      split; [lia|].
      split; [lia|].
      apply I2.
Qed.

Definition rule3_subst_batch(x:rule3)(i0' i1':N->N->N3)(v2:N):list rule3 :=
  rule3_subst_batch_0 x i0' i1' (N.to_nat v2) v2 N0.

Lemma rule3_subst_batch_spec x i0' i1' v2:
  forall j0 j1,
  (j0+j1=v2)%N ->
  In (rule3_subst (i0' j0 j1) (i1' j0 j1) x) (rule3_subst_batch x i0' i1' v2).
Proof.
  intros.
  unfold rule3_subst_batch.
  applys_eq (rule3_subst_batch_spec_0'); lia.
Qed.

Lemma rule3_subst_batch_spec' y x i0' i1' v2:
  In y (rule3_subst_batch x i0' i1' v2) ->
  exists j0 j1,
  (j0+j1=v2)%N /\
  y = rule3_subst (i0' j0 j1) (i1' j0 j1) x.
Proof.
  intros.
  unfold rule3_subst_batch in H.
  epose proof (rule3_subst_batch_spec_0'' _ _ _ _ _ _ H) as [j0 [j1 [I0 [I1 I2]]]].
  exists j0 j1.
  split; auto; lia.
Qed.


Lemma ind_lemma v1 v2 (P:N->N->Prop):
  ((forall j0 j1:N, j0+j1=v2 -> P (v1+j0+1) j1) ->
  (forall i0 i1:N, i0+i1=v1 ->
  (forall j0 j1:N, j0+j1=v2 -> i0+i1=v1 -> P (i0+j0+1) (i1+j1)) ->
  P i0 (i1+v2+1)) ->
  (forall i0 i1:N, i0+i1=v1+v2+1 -> P i0 i1))%N.
Proof.
  intros HO HS i0 i1.
  gen i0.
  induction i1 using N_strong_induction.
  intros i0.
  assert (i1<=v2\/v2<i1)%N as [E|E] by lia.
  - specialize (HO (i0-v1-1) i1)%N.
    intro E0.
    applys_eq HO; lia.
  - specialize (HS i0 (i1-v2-1))%N.
    intro E0.
    applys_eq HS; try lia.
    intros j0 j1 E1 E2.
    applys_eq H; try lia.
Qed.

Definition rule3_subst_ind_O(x:rule3)(v1 v2:N):list rule3 :=
  (rule3_subst_batch x (fun j0 j1 => (1,0,0)) (fun j0 j1 => (0,0,j1)) v2)%N.

Definition rule3_subst_ind_S_H(x:rule3)(v2:N):(list rule3) :=
  (rule3_subst_batch x (fun j0 j1 => (1,0,j0+1)) (fun j0 j1 => (0,1,j1)) v2)%N.

Definition rule3_subst_ind_S_G(x:rule3)(v2:N):(rule3) :=
  (rule3_subst (1,0,0) (0,1,v2+1) x)%N.

Definition rule3_ind(x:rule3)(v2:N) :=
let '(c12,c3,c4):=x in
if (c4<=?v2)%N then None else
if eqb c3 (1,1,0)%N then
let v1:=(c4-v2-1)%N in
Some (rule3_subst_ind_O x v1 v2,
rule3_subst_ind_S_H x v2,
rule3_subst_ind_S_G x v2)
else None.


Lemma rule3_ind_spec x v2:
match rule3_ind x v2 with
| None => True
| Some (G0,H,G) =>
  forall tm C,
  (forall i0 i1, Forall (fun x => rule3_to_pred tm C x i0 i1) G0) ->
  (forall i0 i1,
    Forall (fun x => rule3_to_pred tm C x i0 i1) H ->
    rule3_to_pred tm C G i0 i1) ->
  (forall i0 i1, rule3_to_pred tm C x i0 i1)
end.
Proof.
  destruct x as [[c12 c3] c4].
  unfold rule3_ind.
  destruct (N.leb_spec c4 v2) as [E|E]; trivial.
  destruct (eqb_spec c3 (1,1,0)%N); trivial.
  subst c3.
  intros tm C.
  remember (c4-v2-1)%N as v1.
  replace c4 with (v1+v2+1)%N by lia. clear Heqv1 E c4.
  unfold rule3_to_pred.
  epose proof (ind_lemma (v1+C) v2 (fun i0 i1 => rule3_to_pred_0 tm c12 i0 i1)) as I.
  cbn in I.
  intros G0 G1 i0 i1 Heq.
  cbn - [N.mul] in Heq.
  apply I; clear I.
  3: lia.
  - clear G1.
    clear Heq i0 i1.
    intros j0 j1 Hj.
    eassert (H:forall i0 i1:N,_). {
      intros i2 i3.
      specialize (G0 i2 i3).
      rewrite Forall_forall in G0.
      epose proof (rule3_subst_batch_spec _ _ _ v2 j0 j1 Hj) as HIn.
      specialize (G0 _ HIn).
      clear HIn.
      epose proof (rule3_subst_spec tm C _ _ (c12,(1,1,0),v1+v2+1)%N _ _) as H.
      unfold rule3_to_pred in H.
      rewrite H in G0. clear H.
      cbn - [N.mul] in G0.
      simpl_N_add_mul.
      exact G0.
    }
    clear G0.
    applys_eq H.
    2: lia.
    1: exact N0.
  - clear G0.
    clear Heq i0 i1.
    intros i0 i1 Hi H.
    specialize (G1 i0 i1).
    unfold rule3_subst_ind_S_H in G1.
    unfold rule3_subst_ind_S_G in G1.
    epose proof (rule3_subst_spec tm C _ _ (c12,(1,1,0),v1+v2+1)%N _ _) as H'.
    unfold rule3_to_pred in H'.
    rewrite H' in G1. clear H'.
    cbn - [N.mul] in G1.
    simpl_N_add_mul.
    applys_eq G1; try lia.
    clear G1.
    rewrite Forall_forall.
    intros x HIn.
    epose proof (rule3_subst_batch_spec' _ _ _ _ _ HIn) as [j0 [j1 [I1 I2]]].
    subst x.
    clear HIn.
    epose proof (rule3_subst_spec tm C _ _ (c12,(1,1,0),v1+v2+1) _ _)%N as H'.
    unfold rule3_to_pred in H'.
    rewrite H'.
    clear H'.
    cbn - [N.mul].
    simpl_N_add_mul.
    intro H0.
    rewrite N.add_assoc.
    apply H; auto; lia.
Qed.


Fixpoint simpl_seg2_rot_0(x0:seg)(y:N3)(a:seg2):seg2 :=
match a,x0 with
| h::t,xh::xt =>
  if eqb h ([xh],N3_1)%N then
    h::simpl_seg2_rot_0 (xt++[xh]) y t
  else
    (x0,y)::a
| _,_ => (x0,y)::a
end.

Fixpoint simpl_seg2_rot(a:seg2):seg2 :=
match a with
| (x0,y0)::t =>
  let t := simpl_seg2_rot t in
  if eqb y0 N3_1 then (x0,y0)::t
  else simpl_seg2_rot_0 x0 y0 t
| _ =>nil
end.

Fixpoint simpl_seg2_merge(a:seg2):seg2 :=
match a with
| (x0,y0)::t =>
  let t := simpl_seg2_merge t in
  match t with
  | (x1,y1)::t0 =>
    if eqb x0 x1 then
      (x0,N3add y0 y1)::t0
    else (x0,y0)::t
  | _ => (x0,y0)::t
  end
| _ => nil
end.

Definition seg2_entry_unfold_O(a:seg*N3):seg2 :=
if eqb (snd a) N3_0 then [] else [a].

Definition seg2_entry_unfold(a:seg*N3):seg2 :=
let '(x0,(y0,y)) := a in
(map (fun x => ([x],N3_1)) x0)^^(N.to_nat y) ++
seg2_entry_unfold_O (x0,(y0,0)%N).

Definition simpl_seg2_unfold(a:seg2):seg2 :=
flat_map seg2_entry_unfold a.

Definition simpl_seg2(a:seg2):seg2 :=
let a := simpl_seg2_unfold a in
let a := simpl_seg2_rot a in
let a := simpl_seg2_merge a in
a.

Definition simpl_config2(a:config2):config2 :=
let '(l,r,s,sgn):=a in
(simpl_seg2 l,simpl_seg2 r,s,sgn).

Lemma lpow_cons_app{T}(h:T)(t t0:list T) n:
  (h::t)^^n ++ h :: t0 =
  h::(t++[h])^^n ++ t0.
Proof.
  induction n.
  1: reflexivity.
  cbn.
  repeat rewrite <-List.app_assoc.
  rewrite IHn.
  reflexivity.
Qed.

Local Opaque eqb.
Lemma simpl_seg2_rot_spec a i0 i1:
  seg2_csubst i0 i1 a =
  seg2_csubst i0 i1 (simpl_seg2_rot a).
Proof.
  induction a as [|[x0 y0] t].
  1: reflexivity.
  cbn.
  destruct (eqb_spec y0 N3_1) as [E|E].
  - cbn.
    congruence.
  - rewrite IHt.
    clear IHt E.
    generalize (simpl_seg2_rot t); clear t; intro t.
    gen x0 y0.
    induction t; intros.
    1: reflexivity.
    cbn.
    destruct x0 as [|xh xt]; trivial.
    destruct (eqb_spec a ([xh],N3_1)) as [E|E]; trivial.
    subst a.
    cbn.
    rewrite <-IHt.
    destruct y0 as [[y0 y1] y].
    change (Pos.to_nat 1) with 1.
    cbn.
    rewrite lpow_cons_app.
    reflexivity.
Qed.

Lemma simpl_seg2_merge_spec a i0 i1:
  seg2_csubst i0 i1 a =
  seg2_csubst i0 i1 (simpl_seg2_merge a).
Proof.
  induction a as [|[x0 y0] t].
  1: reflexivity.
  cbn.
  rewrite IHt.
  destruct (simpl_seg2_merge t) as [|[x1 y1] t0]; trivial.
  cbn.
  destruct (eqb_spec x0 x1); trivial.
  subst.
  destruct y0 as [[y00 y01] y0].
  destruct y1 as [[y10 y11] y1].
  cbn.
  rewrite List.app_assoc.
  rewrite <-lpow_add.
  repeat (lia || f_equal).
Qed.

Lemma simpl_seg2_unfold_spec a i0 i1:
  seg2_csubst i0 i1 a =
  seg2_csubst i0 i1 (simpl_seg2_unfold a).
Proof.
  induction a as [|[x0 y0] t].
  1: reflexivity.
  cbn.
  rewrite IHt.
  unfold simpl_seg2_unfold.
  destruct y0 as [[y0 y1] y].
  rewrite seg2_csubst_app.
  f_equal.
  rewrite Nnat.N2Nat.inj_add.
  rewrite Nat.add_comm.
  induction y using N.peano_ind.
  - cbn.
    unfold seg2_entry_unfold_O,snd.
    destruct (eqb_spec (y0,y1,0%N) N3_0).
    + inverts e.
      reflexivity.
    + cbn.
      rewrite app_nil_r.
      f_equal. lia.
  - rewrite Nnat.N2Nat.inj_succ.
    cbn[Nat.add].
    cbn[lpow].
    rewrite <-app_assoc.
    rewrite seg2_csubst_app.
    rewrite <-IHy.
    f_equal.
    clear IHy IHt.
    induction x0; trivial.
    cbn.
    rewrite <-IHx0.
    reflexivity.
Qed.

Lemma simpl_seg2_spec a i0 i1:
  seg2_csubst i0 i1 a =
  seg2_csubst i0 i1 (simpl_seg2 a).
Proof.
  unfold simpl_seg2.
  rewrite <-simpl_seg2_merge_spec.
  rewrite <-simpl_seg2_rot_spec.
  rewrite <-simpl_seg2_unfold_spec.
  reflexivity.
Qed.

Lemma simpl_config2_spec a i0 i1:
  config2_csubst i0 i1 a =
  config2_csubst i0 i1 (simpl_config2 a).
Proof.
  destruct a as [[[l r] s] sgn].
  cbn.
  repeat rewrite <-simpl_seg2_spec.
  reflexivity.
Qed.

Definition solve_config2_eq(a b:config2):bool :=
eqb (simpl_config2 a) (simpl_config2 b).

Lemma solve_config2_eq_spec a b:
if solve_config2_eq a b then
  forall i0 i1, config2_csubst i0 i1 a = config2_csubst i0 i1 b
else True.
Proof.
  unfold solve_config2_eq.
  destruct (eqb_spec (simpl_config2 a) (simpl_config2 b)); trivial.
  intros.
  rewrite simpl_config2_spec.
  rewrite e.
  rewrite <-simpl_config2_spec.
  reflexivity.
Qed.

(*
Definition solve_rule2(H G:rule2):bool :=
let '(c12,(a0,a1,a),c4):=H in
let '(c12',(b0,b1,b),c4'):=G in
solve_config2_eq c12 c12' &&
*)


Definition listZ2N(ls:list Z):option (list N) :=
if forallb (Z.leb Z0) ls then Some (map Z.to_N ls) else None.

Definition seg2_from_id_args(x:int)(y0 y1 y:seg1y)(id:Seg1xIdAlloc.id_alloc_t):option seg2 :=
listZ2N y0 &&& (fun y0 =>
listZ2N y1 &&& (fun y1 =>
listZ2N y &&& (fun y =>
Seg1xIdAlloc.get_key x id &&& (fun x' => Some (combine x' (combine (combine y0 y1) y)))))).

Definition config2_from_id_args(x:Config0.Tx)(y0 y1 y:Config0.Ty)(id:Seg1xIdAlloc.id_alloc_t):option config2 :=
let '(l,r,s,sgn):=x in
seg2_from_id_args l (fst y0) (fst y1) (fst y) id &&& (fun l =>
seg2_from_id_args r (snd y0) (snd y1) (snd y) id &&& (fun r =>
Some (l,r,s,sgn)
)).

Definition make_rule2(tx:Config0.Tx*Config0.Tx)(ty0 ty1 ty:Config0.Ty*Config0.Ty)(cond:N3)(tp:N*N+N)(id:Seg1xIdAlloc.id_alloc_t):option rule2 :=
config2_from_id_args (fst tx) (fst ty0) (fst ty1) (fst ty) id &&& (fun c1 =>
config2_from_id_args (snd tx) (snd ty0) (snd ty1) (snd ty) id &&& (fun c2 =>
Some (c1,c2,cond,tp)
)).


Definition seg2_4_from_id_args(x:int*int*int*int)(y0 y1 y:seg1y*seg1y*seg1y*seg1y)(id:Seg1xIdAlloc.id_alloc_t):option (seg2*seg2*seg2*seg2) :=
let '(x0,x1,x2,x3):=x in
let '(y00,y01,y02,y03):=y0 in
let '(y10,y11,y12,y13):=y1 in
let '(y0,y1,y2,y3):=y in
seg2_from_id_args x0 y00 y10 y0 id &&& (fun v0 =>
seg2_from_id_args x1 y01 y11 y1 id &&& (fun v1 =>
seg2_from_id_args x2 y02 y12 y2 id &&& (fun v2 =>
seg2_from_id_args x3 y03 y13 y3 id &&& (fun v3 =>
Some (v0,v1,v2,v3))))).


Definition rule2_subst1(x:rule2)(l r:seg2):rule2 :=
let '(x1,x2,c3,c4):=x in
let '(l1,r1,s1,sgn1):=x1 in
let '(l2,r2,s2,sgn2):=x2 in
let (l',r'):=(if eqb sgn1 sgn2 then (l,r) else (r,l)) in
(
(l1++l,r1++r,s1,sgn1),
(l2++l',r2++r',s2,sgn2),
c3,c4
).

Definition rule2_subst2(x:rule2)(l r:seg2):rule2 :=
let '(x1,x2,c3,c4):=x in
let '(l1,r1,s1,sgn1):=x1 in
let '(l2,r2,s2,sgn2):=x2 in
let (l',r'):=(if eqb sgn1 sgn2 then (l,r) else (r,l)) in
(
(l1++l',r1++r',s1,sgn1),
(l2++l,r2++r,s2,sgn2),
c3,c4
).

Lemma rule2_subst1_spec tm c i0 i1 x l r:
  rule2_to_pred tm c x i0 i1 ->
  rule2_to_pred tm c (rule2_subst1 x l r) i0 i1.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c1 as [[[l1 r1] s1] sgn1].
  destruct c2 as [[[l2 r2] s2] sgn2].
  cbn.
  intros H.
  unfold rule2_to_pred.
  destruct (eqb_spec sgn1 sgn2);
  destruct sgn1,sgn2; try congruence;
  intros H0;
  specialize (H H0); clear H0;
  cbn; intros;
  repeat rewrite seg2_csubst_app;
  repeat rewrite Str_app_assoc;
  apply H.
Qed.

Lemma rule2_subst2_spec tm c i0 i1 x l r:
  rule2_to_pred tm c x i0 i1 ->
  rule2_to_pred tm c (rule2_subst2 x l r) i0 i1.
Proof.
  destruct x as [[[c1 c2] c3] c4].
  destruct c1 as [[[l1 r1] s1] sgn1].
  destruct c2 as [[[l2 r2] s2] sgn2].
  cbn.
  intros H.
  unfold rule2_to_pred.
  destruct (eqb_spec sgn1 sgn2);
  destruct sgn1,sgn2; try congruence;
  intros H0;
  specialize (H H0); clear H0;
  cbn; intros;
  repeat rewrite seg2_csubst_app;
  repeat rewrite Str_app_assoc;
  apply H.
Qed.


Section rule4_ctx.
Hypothesis tm:TM.
Definition list_rule2_to_prop C (x:rule2ls):Prop :=
Forall (rule2_to_prop tm C) x.

Definition pair_list_rule2_to_prop C (x:rule2ls*rule2ls):Prop :=
let '(x0,x1):=x in
list_rule2_to_prop C x0 /\ list_rule2_to_prop C x1.

Definition rule4_to_prop C (x:rule4):Prop :=
Forall (pair_list_rule2_to_prop C) x.

Definition rule4_to_list_rule2(x:rule4):list rule2 :=
flat_map (fun '(a,b) => a++b) x.

Lemma rule4_to_list_rule2_spec C x:
  rule4_to_prop C x <->
  list_rule2_to_prop C (rule4_to_list_rule2 x).
Proof.
  unfold rule4_to_prop.
  unfold list_rule2_to_prop.
  induction x as [|[a b] x].
  - cbn.
    simpl_Forall.
    tauto.
  - cbn.
    simpl_Forall.
    unfold pair_list_rule2_to_prop.
    tauto.
Qed.

Fixpoint list_rule2_to_list_rule0(x:list rule2):option (list Rule0.T) :=
match x with
| nil => Some []
| h::t =>
  rule2_to_list_rule0 MAXT h &&& (fun v =>
  list_rule2_to_list_rule0 t &&& (fun v' =>
  Some (v++v')))
end.

Lemma list_rule2_to_list_rule0_spec x:
match list_rule2_to_list_rule0 x with
| None => True
| Some v =>
  Forall (fun x => Rule0.to_prop x tm) v ->
  list_rule2_to_prop N0 x
end.
Proof.
  unfold list_rule2_to_prop.
  induction x.
  - cbn.
    simpl_Forall.
    tauto.
  - cbn[list_rule2_to_list_rule0].
    unfold if_Some.
    destruct_spec (rule2_to_list_rule0_spec tm); trivial.
    destruct_spec list_rule2_to_list_rule0; trivial.
    simpl_Forall.
    tauto.
Qed.

Definition subst_rule4_Sc(x:rule4):rule4 :=
map (fun '(a,b) => (map rule2_subst_Sc a,map rule2_subst_Sc b)) x.

Lemma subst_rule4_Sc_spec C x:
rule4_to_prop C (subst_rule4_Sc x) <-> rule4_to_prop (C+1)%N x.
Proof.
  unfold rule4_to_prop.
  unfold subst_rule4_Sc.
  induction x as [|[a b] x].
  - simpl_Forall.
    tauto.
  - cbn[map].
    simpl_Forall.
    rewrite IHx.
    unfold pair_list_rule2_to_prop.
    assert (H':forall a,
      list_rule2_to_prop C (map rule2_subst_Sc a) <->
      list_rule2_to_prop (C+1)%N a). {
      clear IHx x a b.
      unfold list_rule2_to_prop.
      induction a.
      1: simpl_Forall; tauto.
      cbn.
      simpl_Forall.
      rewrite <-IHa.
      rewrite rule2_subst_Sc_spec.
      tauto.
    }
    repeat rewrite H'.
    tauto.
Qed.

Fixpoint list_rule2_lt_r_S(H G:rule2ls){struct G}:option rule2ls :=
match G,H with
| [],_ => Some []
| G0::G1,H0::H1 =>
  rule2_lt_r_S G0 &&& (fun '(G_eq,G_lt) =>
  if eqb G_lt H0 then
  list_rule2_lt_r_S H1 G1 &&& (fun v' =>
  Some (G_eq::v'))
  else None)
| _,_ => None
end.

Definition pair_list_rule2_lt_r_S(H G:rule2ls*rule2ls):option (rule2ls*rule2ls) :=
let (H0,H1):=H in
let (G0,G1):=G in
list_rule2_lt_r_S H0 G0 &&& (fun v0 =>
list_rule2_lt_r_S H1 G1 &&& (fun v1 =>
Some (v0,v1))).

Fixpoint rule4_lt_r_S(H G:rule4){struct G}:option rule4 :=
match G,H with
| [],_ => Some []
| G0::G1,H0::H1 =>
  pair_list_rule2_lt_r_S H0 G0 &&& (fun v =>
  rule4_lt_r_S H1 G1 &&& (fun v' =>
  Some (v::v')))
| _,_ => None
end.

Lemma list_rule2_lt_r_S_spec C H G:
match list_rule2_lt_r_S H G with
| None => True
| Some G' =>
  (list_rule2_to_prop C H ->
  list_rule2_to_prop C G') ->
  list_rule2_to_prop C H ->
  list_rule2_to_prop C G
end.
Proof with trivial.
  gen H.
  induction G as [|G0 G1]; intros [|H0 H1]; cbn...
  specialize (IHG1 H1).
  unfold if_Some.
  destruct_spec (rule2_lt_r_S_spec)...
  destruct p as [G_eq G_lt].
  destruct (eqb_spec G_lt H0)...
  destruct_spec list_rule2_lt_r_S...
  specialize (H tm C).
  subst G_lt.
  unfold list_rule2_to_prop in *.
  simpl_Forall.
  tauto.
Qed.

Lemma pair_list_rule2_lt_r_S_spec C H G:
match pair_list_rule2_lt_r_S H G with
| None => True
| Some G' =>
  (pair_list_rule2_to_prop C H ->
  pair_list_rule2_to_prop C G') ->
  pair_list_rule2_to_prop C H ->
  pair_list_rule2_to_prop C G
end.
Proof.
  destruct H as [H0 H1].
  destruct G as [G0 G1].
  cbn.
  unfold if_Some.
  destruct_spec (list_rule2_lt_r_S_spec C); trivial.
  destruct_spec (list_rule2_lt_r_S_spec C); trivial.
  unfold pair_list_rule2_to_prop.
  tauto.
Qed.

Lemma rule4_lt_r_S_spec C H G:
match rule4_lt_r_S H G with
| None => True
| Some G' =>
  (rule4_to_prop C H ->
  rule4_to_prop C G') ->
  rule4_to_prop C H ->
  rule4_to_prop C G
end.
Proof.
  gen H.
  induction G as [|G0 G1]; intros [|H0 H1]; cbn; trivial.
  specialize (IHG1 H1).
  unfold if_Some.
  destruct_spec (pair_list_rule2_lt_r_S_spec C); trivial.
  destruct_spec rule4_lt_r_S; trivial.
  unfold rule4_to_prop in *.
  simpl_Forall.
  tauto.
Qed.

Definition rule2_i0_O_S' x :=
(let (x0,x1):=rule2_i0_O_S x in
let x0:=rule2_subst (0,1,0) (1,0,0) x0 in
(x0,x1))%N.

Fixpoint list_rule2_i0_O_S_n(x:rule2ls)(n:nat):rule2ls*rule4 :=
match n with
| O => (x,[])
| S n =>
  let (xO,xS):=split (map rule2_i0_O_S' x) in
  let (a,b):=list_rule2_i0_O_S_n xS n in
  (a,(xO,[])::b)
end.

Definition list_rule2_ind(x:list rule2)(k0 k1:N):option (rule4*((list rule3)*rule3)*rule4*(list rule2)) :=
  let (x1,G1) := list_rule2_i0_O_S_n x (N.to_nat k1) in
  rule3_from_list_rule2 x1 &&& (fun x1' =>
  rule3_ind x1' k0 &&& (fun '(G0,H,G) =>
  let G0:=map (fun x => (rule3_to_list_rule2 x,[])) G0 in
  Some (G0,(H,G),G1,x1))).

Lemma rule2_i0_O_S'_spec C x:
  let (x0,x1):=rule2_i0_O_S' x in
  rule2_to_prop tm C x0 ->
  rule2_to_prop tm C x1 ->
  rule2_to_prop tm C x.
Proof.
  unfold rule2_i0_O_S'.
  pose proof (rule2_i0_O_S_spec tm C x).
  unfold rule2_i0_O_S.
  intros.
  apply H; auto.
  unfold rule2_to_prop in *.
  intros.
  specialize (H0 i1 i0).
  clear H1 H.
  rewrite rule2_subst_spec in H0.
  cbn - [N.mul] in *.
  simpl_N_add_mul.
  apply H0.
Qed.

Lemma list_rule2_i0_O_S_n_spec C x n:
let (a,b):=list_rule2_i0_O_S_n x n in
list_rule2_to_prop C a ->
rule4_to_prop C b ->
list_rule2_to_prop C x.
Proof.
  gen x.
  induction n; intros.
  1: cbn; tauto.
  cbn.
  destruct (split (map rule2_i0_O_S' x)) as [xO xS] eqn:E.
  specialize (IHn xS).
  destruct (list_rule2_i0_O_S_n xS n) as [a b].
  intros.
  unfold rule4_to_prop in *.
  simpl_Forall.
  unfold pair_list_rule2_to_prop in *.
  destruct H0 as [[H0a _] H0b].
  specialize (IHn H H0b). clear H H0b.
  gen xO xS.
  unfold list_rule2_to_prop.
  induction x; intros; simpl_Forall; trivial.
  cbn[map] in E.
  cbn[split] in E.
  pose proof (rule2_i0_O_S'_spec C a0) as H.
  destruct (rule2_i0_O_S' a0) as [xO' xS'] eqn:E0.
  inverts E0.
  destruct (split (map rule2_i0_O_S' x)) as [xO'' xS''].
  inverts E.
  simpl_Forall.
  unshelve epose proof (IHx _ _ _ _ eq_refl) as IHx'; tauto.
Qed.

Lemma rule3_from_list_rule2_spec' C x:
match rule3_from_list_rule2 x with
| None => True
| Some y =>
  (forall i0 i1, rule3_to_pred tm C y i0 i1) <->
  list_rule2_to_prop C x
end.
Proof.
  pose proof (rule3_from_list_rule2_spec tm C x) as H.
  destruct_spec rule3_from_list_rule2; trivial.
  unfold list_rule2_to_prop.
  unfold rule2_to_prop.
  split; intros;
  rewrite Forall_forall in *; intros.
  - specialize (H i0 i1).
    specialize (H0 i0 i1).
    rewrite H in H0.
    rewrite Forall_forall in *.
    apply H0; tauto.
  - rewrite H.
    rewrite Forall_forall in *.
    intros.
    apply H0; tauto.
Qed.

Lemma rule3_to_list_rule2_spec' C x:
  (forall i0 i1, rule3_to_pred tm C x i0 i1) <->
  list_rule2_to_prop C (rule3_to_list_rule2 x).
Proof.
  pose proof (rule3_to_list_rule2_spec tm C x) as H.
  unfold list_rule2_to_prop.
  unfold rule2_to_prop.
  split; intros;
  rewrite Forall_forall in *; intros.
  - specialize (H i0 i1).
    specialize (H0 i0 i1).
    rewrite H in H0.
    rewrite Forall_forall in *.
    apply H0; tauto.
  - rewrite H.
    rewrite Forall_forall in *.
    intros.
    apply H0; tauto.
Qed.

Lemma list_rule2_ind_spec' C x k0 k1:
match list_rule2_ind x k0 k1 with
| None => True
| Some (G0,(H,G),G1,X1) =>
  rule4_to_prop C G0 ->
  (forall i0 i1, Forall (fun x => rule3_to_pred tm C x i0 i1) H -> rule3_to_pred tm C G i0 i1) ->
  list_rule2_to_prop C X1
end.
Proof.
  unfold list_rule2_ind.
  destruct_spec (list_rule2_i0_O_S_n_spec C).
  unfold if_Some.
  destruct_spec (rule3_from_list_rule2_spec' C); trivial.
  destruct_spec (rule3_ind_spec); trivial.
  destruct p0 as [[G0 h0] G].
  specialize (H1 tm C).
  intros.
  rewrite <-H0.
  intros.
  apply H1.
  intros.
  all: try tauto.
  unfold rule4_to_prop in H2.
  rewrite Forall_map in H2.
  unfold pair_list_rule2_to_prop in H2.
  rewrite Forall_forall in *.
  intros.
  specialize (H2 x0 H4).
  rewrite <-rule3_to_list_rule2_spec' in H2.
  apply H2.
Qed.

Lemma list_rule2_ind_spec C x k0 k1:
match list_rule2_ind x k0 k1 with
| None => True
| Some (G0,(H,G),G1,X1) =>
  rule4_to_prop C G0 ->
  rule4_to_prop C G1 ->
  (forall i0 i1, Forall (fun x => rule3_to_pred tm C x i0 i1) H -> rule3_to_pred tm C G i0 i1) ->
  list_rule2_to_prop C x
end.
Proof.
  unfold list_rule2_ind.
  destruct_spec (list_rule2_i0_O_S_n_spec C).
  unfold if_Some.
  destruct_spec (rule3_from_list_rule2_spec' C); trivial.
  destruct_spec (rule3_ind_spec); trivial.
  destruct p0 as [[G0 h0] G].
  specialize (H1 tm C).
  intros.
  apply H; try tauto.
  rewrite <-H0.
  intros.
  apply H1.
  intros.
  all: try tauto.
  unfold rule4_to_prop in H2.
  rewrite Forall_map in H2.
  unfold pair_list_rule2_to_prop in H2.
  rewrite Forall_forall in *.
  intros.
  specialize (H2 x0 H5).
  rewrite <-rule3_to_list_rule2_spec' in H2.
  apply H2.
Qed.


Fixpoint rule4_add(x:rule4)(i:int)(y:rule2):rule4 :=
match x with
| (hx,hy)::t =>
    if eqb i int0 then (hx++[y],hy)::t
  else (hx,hy)::(rule4_add t (Uint63.pred i) y)
| nil => nil
end.

Fixpoint rule4_upd(x:rule4)(i:int)(y:rule2ls):rule4 :=
match x with
| (hx,hy)::t =>
  if eqb i int0 then (hx,y)::t
  else (hx,hy)::(rule4_upd t (Uint63.pred i) y)
| nil => nil
end.

Fixpoint seg2_is_all0(x:seg2):bool :=
match x with
| (hx,hy)::t =>
  eqb hx (repeat s0 (length hx)) &&
  seg2_is_all0 t
| _ => true
end.

Fixpoint seg2_sigma_score(x:seg2):nat :=
match x with
| (hx,((hy0,hy1),hy))::t =>
    (sigma_score_seg hx)*(N.to_nat hy0)+
  (seg2_sigma_score t)
| _ => O
end.


Definition config2_is_init(x:config2):bool :=
let '(l,r,s,sgn):=x in
(eqb s q0 &&
seg2_is_all0 l &&
seg2_is_all0 r)%bool.

Definition config2_sigma_score(x:config2):nat :=
let '(l,r,s,sgn):=x in
(seg2_sigma_score l)+
(seg2_sigma_score r).


Definition rule2_check_sigma_score_0(x:rule2):bool :=
let '(c1,c2,c3,c4):=x in
(match c4 with
| inr r =>
  eqb c3 (1,0,0)%N &&
  config2_is_init c1 &&
  negb (eqb O (config2_sigma_score c2))
| _ => false
end)%bool.

Definition rule2_check_sigma_score(x:rule2):bool :=
match rule2_lt_to_eq x N0 with
| Some w =>
  (rule2_check_sigma_score_0 (rule2_subst (1,0,0)%N N3_0 w) ||
  rule2_check_sigma_score_0 (rule2_subst N3_0 (1,0,0)%N w))%bool
| _ => false
end.

Definition pair_list_rule2_check_sigma_score(x:rule2ls*rule2ls):bool :=
let (x0,x1):=x in
(existsb rule2_check_sigma_score x0 ||
existsb rule2_check_sigma_score x1)%bool.

Definition rule4_check_sigma_score(x:rule4):bool :=
existsb pair_list_rule2_check_sigma_score x.

Lemma seg2_is_all0_spec x:
if seg2_is_all0 x then
forall i0 i1, seg2_csubst i0 i1 x *> const s0 = const s0
else True.
Proof.
  induction x as [|[x0 [[y0 y1] y]] x].
  - cbn.
    trivial.
  - cbn.
    destruct (eqb_spec x0 (repeat s0 (length x0))); trivial.
    destruct_spec seg2_is_all0; trivial.
    intros.
    specialize (IHx i0 i1).
    rewrite Str_app_assoc.
    rewrite IHx.
    clear IHx H.
    generalize (N.to_nat (y0*i0+y1*i1+y))%N. 
    induction n.
    1: reflexivity.
    cbn.
    rewrite Str_app_assoc.
    rewrite IHn. clear IHn.
    induction x0.
    1: reflexivity.
    cbn in *.
    inverts e.
    specialize (IHx0 H1).
    rewrite <-H1.
    rewrite IHx0.
    rewrite <-const_unfold.
    reflexivity.
Qed.

Lemma config2_is_init_spec x:
if config2_is_init x then
forall i0 i1, Config0.to_config (config2_csubst i0 i1 x) (const s0) (const s0) = c0
else True.
Proof.
  unfold config2_is_init.
  destruct x as [[[l r] s] sgn].
  destruct (eqb_spec s q0); trivial.
  subst.
  destruct_spec seg2_is_all0_spec; trivial.
  destruct_spec seg2_is_all0_spec; trivial.
  intros.
  cbn.
  destruct sgn;
  rewrite H,H0;
  reflexivity.
Qed.

Lemma seg2_sigma_score_spec x i0 i1:
(seg2_sigma_score x)*(N.to_nat i0) <=
(sigma_score_seg (seg2_csubst i0 i1 x)).
Proof.
  induction x as [|[x0 [[y0 y1] y]] x].
  1: reflexivity.
  cbn in *.
  rewrite Nat.mul_add_distr_r.
  rewrite sigma_score_app.
  rewrite (sigma_score_lpow x0 (N.to_nat (y0*i0+y1*i1+y)) _ eq_refl).
  lia.
Qed.

Lemma config2_is_sigma_score_unbounded_spec x i0 i1:
exists n,
sigma_score (Config0.to_config (config2_csubst i0 i1 x) (const s0) (const s0)) n /\
(config2_sigma_score x)*(N.to_nat i0) <= n.
Proof.
  destruct x as [[[l r] s] sgn].
  cbn.
  pose proof (seg2_sigma_score_spec l i0 i1).
  pose proof (seg2_sigma_score_spec r i0 i1).
  destruct sgn.
  - eexists.
    split.
    + solve_sigma_score.
    + lia.
  - eexists.
    split.
    + solve_sigma_score.
    + lia.
Qed.

Lemma rule2_check_sigma_score_0_spec x:
if rule2_check_sigma_score_0 x then
(forall C, rule2_to_prop tm C x) ->
~halts tm c0
else True.
Proof.
  unfold rule2_check_sigma_score_0.
  destruct x as [[[c1 c2] c3] c4].
  destruct c4 as [|r]; trivial.
  destruct (eqb_spec c3 (1,0,0))%N; trivial.
  destruct_spec config2_is_init_spec; trivial.
  pose proof (config2_is_sigma_score_unbounded_spec c2).
  destruct (eqb_spec 0 (config2_sigma_score c2)); cbn; trivial.
  intros.
  eapply sigma_score_unbounded_nonhalt.
  intros.
  specialize (H1 (N.of_nat n0)).
  unfold rule2_to_prop in H1.
  cbn in H1.
  specialize (H (r+(N.of_nat n0))%N N0).
  specialize (H0 (r+(N.of_nat n0))%N N0).
  destruct H0 as [n1 H0].
  specialize (H1 (r+(N.of_nat n0))%N N0).
  inverts e.
  cbn - [N.mul] in H1.
  simpl_N_add_mul.
  specialize (H1 eq_refl (const s0) (const s0)).
  rewrite H in H1.
  destruct H0 as [H0 H0a].
  eexists _,_.
  split.
  - apply H1.
  - split.
    + apply H0.
    + remember (config2_sigma_score c2) as v1.
      destruct v1 as [|v1]; lia.
Qed.

Lemma rule2_check_sigma_score_spec x:
if rule2_check_sigma_score x then
(forall C, rule2_to_prop tm C x) ->
~halts tm c0
else True.
Proof.
  unfold rule2_check_sigma_score.
  destruct_spec rule2_lt_to_eq_spec; trivial.
  destruct_spec rule2_check_sigma_score_0_spec.
  - intros.
    apply H0.
    intros.
    unfold rule2_to_prop in *.
    intros.
    rewrite rule2_subst_spec.
    apply H,H1.
  - destruct_spec rule2_check_sigma_score_0_spec; trivial.
    intros.
    apply H1.
    intros.
    unfold rule2_to_prop in *.
    intros.
    rewrite rule2_subst_spec.
    apply H,H2.
Qed.

Lemma pair_list_rule2_check_sigma_score_spec x:
if pair_list_rule2_check_sigma_score x then
(forall C, pair_list_rule2_to_prop C x) ->
~halts tm c0
else True.
Proof.
  unfold pair_list_rule2_check_sigma_score.
  destruct x as [x0 x1].
  destruct_spec existsb_exists.
  - destruct H as [H _].
    specialize (H eq_refl).
    destruct H as [x2 [Hx2 H]].
    intros Hx.
    pose proof (rule2_check_sigma_score_spec x2) as H0.
    rewrite H in H0.
    apply H0.
    intro C.
    specialize (Hx C).
    unfold pair_list_rule2_to_prop,list_rule2_to_prop in Hx.
    rewrite Forall_forall in Hx.
    intuition.
  - clear H.
    destruct_spec existsb_exists; trivial.
    destruct H as [H _].
    specialize (H eq_refl).
    destruct H as [x2 [Hx2 H]].
    intros Hx.
    pose proof (rule2_check_sigma_score_spec x2) as H0.
    rewrite H in H0.
    apply H0.
    intro C.
    specialize (Hx C).
    unfold pair_list_rule2_to_prop,list_rule2_to_prop in Hx.
    repeat rewrite Forall_forall in Hx.
    intuition.
Qed.

Lemma rule4_check_sigma_score_spec x:
if rule4_check_sigma_score x then
(forall C, rule4_to_prop C x) ->
~halts tm c0
else True.
Proof.
  unfold rule4_check_sigma_score.
  destruct_spec existsb_exists; trivial.
  destruct H as [H _].
  specialize (H eq_refl).
  destruct H as [x0 [Hx0 H]].
  intros Hx.
  pose proof (pair_list_rule2_check_sigma_score_spec x0) as H0.
  rewrite H in H0.
  apply H0.
  intro C.
  specialize (Hx C).
  unfold rule4_to_prop in Hx.
  rewrite Forall_forall in Hx.
  intuition.
Qed.

End rule4_ctx.


End seg2_ctx.

Module SegInterpolation.

Fixpoint seg_lcp(a b:seg):nat :=
match a,b with
| a0::a1,b0::b1 =>
  if eqb a0 b0 then S (seg_lcp a1 b1) else O
| _,_ => O
end.

Definition nat_sub(a b:nat):option nat :=
(if a<?b then None else Some (a-b))%nat.

Record seg6 := {
  v00:seg;
  v01:seg;
  v02:seg;
  v10:seg;
  v11:seg;
  v20:seg;
}.

Definition seg6_upd_v20(x:seg6)(y:seg):seg6 :=
let (v00,v01,v02,v10,v11,v20):=x in
let v20:=y in
Build_seg6 v00 v01 v02 v10 v11 v20.

Definition seg6_upd_v02(x:seg6)(y:seg):seg6 :=
let (v00,v01,v02,v10,v11,v20):=x in
let v02:=y in
Build_seg6 v00 v01 v02 v10 v11 v20.

Fixpoint seg_match(a b:seg)(n:nat):bool :=
match n with
| O => true
| S n =>
  match a,b with
  | a0::a1,b0::b1 =>
    (eqb a0 b0 && seg_match a1 b1 n)%bool
  | _,_ =>false
  end
end.

Definition seg6_tl(x:seg6):option (seg6) :=
let (v00,v01,v02,v10,v11,v20):=x in
match v00,v01,v02,v10,v11,v20 with
| h00::t00,h01::t01,h02::t02,h10::t10,h11::t11,h20::t20 =>
  if forallb (eqb h00) [h01;h02;h10;h11;h20] then Some (Build_seg6 t00 t01 t02 t10 t11 t20) else None
| _,_,_,_,_,_ => None
end.

Fixpoint seg6_tl_n(x:seg6)(n m:nat):=
match n with
| S n =>
  match seg6_tl x with
  | Some x => seg6_tl_n x n (S m)
  | None => (x,m)
  end
| _ => (x,m)
end.

Definition seg6_tl_i(x:seg6):option (seg6) :=
let (v00,v01,v02,v10,v11,v20):=x in
match v10,v11,v20 with
| h10::t10,h11::t11,h20::t20 =>
  if (eqb h10 h11 && eqb h11 h20)%bool then
  Some (Build_seg6 v00 v01 v02 t10 t11 t20)
  else None
| _,_,_ => None
end.

Definition seg6_tl_j(x:seg6):option (seg6) :=
let (v00,v01,v02,v10,v11,v20):=x in
match v01,v02,v11 with
| h01::t01,h02::t02,h11::t11 =>
  if (eqb h01 h02 && eqb h02 h11)%bool then
  Some (Build_seg6 v00 t01 t02 v10 t11 v20)
  else None
| _,_,_ => None
end.

Fixpoint seg_sub(x y:seg):option seg :=
match x,y with
| x0::x,y0::y => 
  if eqb x0 y0 then seg_sub x y else None
| _,nil => Some x
| _,_ => None
end.

Definition check_suffix(x y:seg):bool :=
match seg_sub x y with
| Some z =>
  match seg_sub x z with
  | Some _ => false
  | _ => true
  end
| _ => true
end.

Fixpoint is_prime_0(x y:seg):bool :=
match y with
| nil => true
| y0::y1 =>
  check_suffix x y && is_prime_0 x y1
end.

Definition is_prime(x:seg):bool :=
match x with
| x0::x1 => is_prime_0 x x1
| _ => false
end.

Fixpoint seg6_tl_i_n(x x0:seg6)(n m:nat)(res:list (seg6*nat)) :=
match n with
| S n =>
  match seg6_tl_i x with
  | Some x =>
    let m:=S m in
    let res :=
    (if (seg_match x0.(v20) x.(v20) m && is_prime (firstn m x0.(v20)))%bool then
      (x,m)::res
    else res) in
      seg6_tl_i_n x x0 n m res
  | None => res
  end
| _ => res
end.

Fixpoint seg6_tl_j_n(x x0:seg6)(n m:nat)(res:list (seg6*nat)) :=
match n with
| S n =>
  match seg6_tl_j x with
  | Some x =>
    let m:=S m in
    let res :=
    (if (seg_match x0.(v02) x.(v02) m && is_prime (firstn m x0.(v02)))%bool then
      (x,m)::res
    else res) in
      seg6_tl_j_n x x0 n m res
  | None => res
  end
| _ => res
end.

Fixpoint find_first'{A B}(ls:list A)(f:A->option B):option B :=
match ls with
| nil => None
| h::t =>
  f h ||| find_first' t f
end.

Definition push_rep(x:seg*N3)(y:seg2):seg2 :=
let (a0,b0):=x in
match y with
| (a,b)::y0 =>
  if eqb a0 a then (a,N3add b0 b)::y0 else x::y
| _ => x::y
end.

Fixpoint seg_divmod(x y:seg)(T:nat):N*seg:=
match T with
| O => (N0,x)
| S T =>
match seg_sub x y with
| Some z =>
  let (a,b):=seg_divmod z y T in (N.succ a,b)
| None => (N0,x)
end
end.

Definition push_const'(x:seg)(y:seg2):seg2 :=
match x with
| nil => y
| _ => (x,N3_1)::y
end.

Definition push_const(x:seg)(y:seg2):seg2 :=
match y with
| (a,b)::y0 =>
  let (p,q):=seg_divmod (rev x) (rev a) (S(length x)) in
  push_const' (rev q) ((a,N3add b (N0,N0,p))::y0)
| _ => push_const' x y
end.

Fixpoint calc(x:seg6)(l l0 l1:nat)(T:nat):option seg2 :=
if (eqb l O && eqb l0 O && eqb l1 O)%bool then Some []
else
match T with
| O => None
| S T =>
let (x',m):=seg6_tl_n x l O in
match m with
| O =>
  find_first' (seg6_tl_i_n x x l0 O []) (fun '(x',m) =>
    calc (seg6_upd_v20 x' (skipn m x'.(v20))) l (l0-m)%nat l1 T &&& (fun v =>
    Some (push_rep (firstn m x'.(v20),(1,0,0)%N) v))) |||
  find_first' (seg6_tl_j_n x x l1 O []) (fun '(x',m) =>
    calc (seg6_upd_v02 x' (skipn m x'.(v02))) l l0 (l1-m)%nat T &&& (fun v =>
    Some (push_rep (firstn m x'.(v02),(0,1,0)%N) v)))
| S _ =>
  calc x' (l-m)%nat l0 l1 T &&& (fun v =>
  Some (push_const (firstn m x.(v00)) v))
end
end.

Section subst_ctx.
Hypothesis i0_dec i1_dec:N.

Fixpoint seg_subst_dec(ls:seg2):option seg2 :=
match ls with
| (a,((y0,y1),y))::t =>
  let dy := (y0*i0_dec+y1*i1_dec)%N in
  if N.ltb y dy then None
  else seg_subst_dec t &&& (fun v =>
  Some ((a,((y0,y1),y-dy))::v))%N
| nil => Some nil
end.

Definition to_seg2_6(v00 v01 v02 v10 v11 v20:seg):option seg2 :=
let l:=length v00 in
nat_sub (length v10) l &&& (fun l0 =>
nat_sub (length v01) l &&& (fun l1 =>
if (
eqb (length v02) (l1+l1+l)%nat &&
eqb (length v11) (l0+l1+l)%nat &&
eqb (length v20) (l0+l0+l)%nat)%bool
then
calc (Build_seg6 v00 v01 v02 v10 v11 v20) l l0 l1 (S(l0+l1+l))%nat &&&
seg_subst_dec
else None
)).

Definition to_seg2_3(v0 v1 v2:seg):option seg2 :=
  to_seg2_6 v0 v0 v0 v1 v1 v2.

Definition to_config2_6(v00 v01 v02 v10 v11 v20:Config0.T):option config2 :=
let '(l00,r00,s00,sgn00):=v00 in
let '(l01,r01,s01,sgn01):=v01 in
let '(l02,r02,s02,sgn02):=v02 in
let '(l10,r10,s10,sgn10):=v10 in
let '(l11,r11,s11,sgn11):=v11 in
let '(l20,r20,s20,sgn20):=v20 in
if (
eqb (s00,sgn00) (s01,sgn01) &&
eqb (s00,sgn00) (s02,sgn02) &&
eqb (s00,sgn00) (s10,sgn10) &&
eqb (s00,sgn00) (s11,sgn11) &&
eqb (s00,sgn00) (s20,sgn20))%bool then
to_seg2_6 l00 l01 l02 l10 l11 l20 &&& (fun l =>
to_seg2_6 r00 r01 r02 r10 r11 r20 &&& (fun r =>
Some (l,r,s00,sgn00)))
else None.

Definition to_config2_3(v0 v1 v2:Config0.T):option config2 :=
let '(l0,r0,s0,sgn0):=v0 in
let '(l1,r1,s1,sgn1):=v1 in
let '(l2,r2,s2,sgn2):=v2 in
if (eqb (s0,sgn0) (s1,sgn1) && eqb (s0,sgn0) (s2,sgn2))%bool then
to_seg2_3 l0 l1 l2 &&& (fun l =>
to_seg2_3 r0 r1 r2 &&& (fun r =>
Some (l,r,s0,sgn0)))
else None.

Definition to_4seg2_6(v00 v01 v02 v10 v11 v20:seg*seg*seg*seg):option (seg2*seg2*seg2*seg2) :=
let '(a00,b00,c00,d00):=v00 in
let '(a01,b01,c01,d01):=v01 in
let '(a02,b02,c02,d02):=v02 in
let '(a10,b10,c10,d10):=v10 in
let '(a11,b11,c11,d11):=v11 in
let '(a20,b20,c20,d20):=v20 in
to_seg2_6 a00 a01 a02 a10 a11 a20 &&& (fun a =>
to_seg2_6 b00 b01 b02 b10 b11 b20 &&& (fun b =>
to_seg2_6 c00 c01 c02 c10 c11 c20 &&& (fun c =>
to_seg2_6 d00 d01 d02 d10 d11 d20 &&& (fun d =>
Some (a,b,c,d))))).

Definition to_4seg2_3(v0 v1 v2:seg*seg*seg*seg):option (seg2*seg2*seg2*seg2) :=
let '(a0,b0,c0,d0):=v0 in
let '(a1,b1,c1,d1):=v1 in
let '(a2,b2,c2,d2):=v2 in
to_seg2_3 a0 a1 a2 &&& (fun a =>
to_seg2_3 b0 b1 b2 &&& (fun b =>
to_seg2_3 c0 c1 c2 &&& (fun c =>
to_seg2_3 d0 d1 d2 &&& (fun d =>
Some (a,b,c,d))))).


Definition to_rule2_6(v00 v01 v02 v10 v11 v20:Config0.T*Config0.T) c3 c4: option rule2 :=
to_config2_6 (fst v00) (fst v01) (fst v02) (fst v10) (fst v11) (fst v20) &&& (fun c1 =>
to_config2_6 (snd v00) (snd v01) (snd v02) (snd v10) (snd v11) (snd v20) &&& (fun c2 =>
Some (c1,c2,c3,c4))).

Definition to_rule2_3(v0 v1 v2:Config0.T*Config0.T) c3 c4: option rule2 :=
to_config2_3 (fst v0) (fst v1) (fst v2) &&& (fun c1 =>
to_config2_3 (snd v0) (snd v1) (snd v2) &&& (fun c2 =>
Some (c1,c2,c3,c4))).

End subst_ctx.

End SegInterpolation.
Import PArray.


Record State := {
  seg1x_id: Seg1xIdAlloc.id_alloc_t;
  rule0_id: Rule0IdAlloc.id_alloc_t;
  mem: Mem.hmap_t;
  rule0_info: array (option Rule0.info_t);
  rest_T: int;
}.

Section check_loop_ctx.
Hypothesis st: State.
Let info := st.(rule0_info).
Let sid := st.(seg1x_id).
Let rid := st.(rule0_id).

Definition infoz(i:int) :=
info.[i] &&& (fun '(x,y,z) => Some (z)).

Definition infox(i:int) :=
info.[i] &&& (fun '(x,y,z) => Some (x)).

Definition infoy(i:int) :=
info.[i] &&& (fun '(x,y,z) => Some (y)).

Definition segX(x:seg):Z := Z.of_nat (List.length x).
Definition configX(x:Config0.T):=
let '(l,r,s,sgn):=x in
(segX l,segX r,box (s,sgn)).
Definition ruleX(x:Rule0.T) :=
let (x0,x1):=x in
(configX x0,configX x1).
Definition seg4X(x:seg*seg*seg*seg) :=
let '(a,b,c,d):=x in
(segX a,segX b,segX c,segX d).
Definition xyX (xy:Rule0.T*(seg*seg*seg*seg)) :=
let (x,y):=xy in
(ruleX x,seg4X y).

Definition check_loop1_at(i d:int):bool :=
(match info.[i],info.[i-d],info.[i-d*int2],info.[i-d*int3] with
| Some (y0,z0),Some (y1,z1),Some (y2,z2),Some (y3,z3) =>
  let '(y0,y1,y2,y3):=(xyX y0,xyX y1,xyX y2,xyX y3) in
  match sub y0 y1 with
  | None => false
  | Some dy =>
    eqb (Some y2) (sub y1 dy) &&
    eqb (Some y3) (sub y2 dy) &&
    match sub z0 z1,sub z1 z2,sub z2 z3 with
    | Some z01,Some z12,Some z23 =>
      match sub z01 z12 with
      | Some d2z =>
        eqb (Some z23) (sub z12 d2z)
      | _ => false
      end
    | _,_,_ => false
    end
  end
| _,_,_,_ => false
end)%bool.
(*
Definition check_loop1_at(i d:int):bool :=
(match infoz i,infoz (i-d),infoz (i-d*int2),infoz (i-d*int3) with
| Some (z0),Some (z1),Some (z2),Some (z3) =>
    match sub z0 z1,sub z1 z2,sub z2 z3 with
    | Some z01,Some z12,Some z23 =>
      match sub z01 z12 with
      | Some d2z =>
        eqb (Some z23) (sub z12 d2z)
      | _ => false
      end
    | _,_,_ => false
    end
| _,_,_,_ => false
end)%bool.
 *)
Fixpoint check_loop1(i d:int)(n:nat):bool :=
(match n with
| O => true
| S n0 =>
  check_loop1_at i d &&
  check_loop1 (Uint63.pred i) d n0
end)%bool.

Fixpoint expand_loop1(i d:int)(d':nat)(n:nat):int :=
match n with
| O => i
| S n0 =>
  if check_loop1 (i+d) d d' then
    expand_loop1 (i+d) d d' n0
  else i
end.

Fixpoint find_loop1(i d p:int)(d':nat)(n:nat):option (int*nat) :=
if PrimInt63.ltsb (i-d*int4) p then None else
match n with
| O => None
| S n0 =>
  if check_loop1 i d d' then Some (d,d')
  else find_loop1 i (Uint63.succ d) p (S d') n0
end.

Definition loop1_t:Type := int*int*int*int.
Section min_b_ctx.
Hypothesis min_b:int*int.
Fixpoint find_all_loop1_0(i p:int)(n:nat)(ls:list loop1_t) :=
if PrimInt63.lesb (length info) i then ls else
match n with
| O => ls
| S n0 =>
  match find_loop1 i int1 p 1 n with
  | Some (d,d') =>
    let i0 := i-d*int4 in
    let i1 := expand_loop1 i d d' n in
    let b:=(i1-i0)/d in
    if ((b<?(fst min_b)) && (d<?(snd min_b)))%bool then
    find_all_loop1_0 (d+i1) p n0 (ls)
    else
    find_all_loop1_0 (Uint63.succ i1) i1 n0 ((p,i0-p,d,b)::ls)
  | None =>
    find_all_loop1_0 (Uint63.succ i) p n0 ls
  end
end.

Definition find_all_loop1 :=
  find_all_loop1_0 int1 int0 MAXT [].
End min_b_ctx.
Definition check_loop1_in_loop2(x0 x1 x2:loop1_t) :=
let '(p0,a0,d0,b0) := x0 in
let '(p1,a1,d1,b1) := x1 in
let '(p2,a2,d2,b2) := x2 in
(
  (eqb a0 a1 && eqb a1 a2) &&
  (eqb d0 d1 && eqb d1 d2) &&
  (eqb (b0-b1) (b1-b2)) &&
  (PrimInt63.lesb b1 b0)
)%bool.

Fixpoint check_loop2(ls0 ls1 ls2:list loop1_t)(d:nat) :=
(match d with
| O => true
| S d0 =>
  match ls0,ls1,ls2 with
  | h0::t0,h1::t1,h2::t2 =>
    check_loop1_in_loop2 h0 h1 h2 &&
    check_loop2 t0 t1 t2 d0
  | _,_,_ => false
  end
end)%bool.

Fixpoint expand_loop2(ls0 ls1 ls2:list loop1_t) res (d:nat)(T:nat) :=
if check_loop2 ls0 ls1 ls2 d then
match T with
| O => []
| S T0 =>
  expand_loop2 ls1 ls2 (skipn d ls2) (ls2::res) d T0
end
else res.

Fixpoint find_loop2_0(ls0:list loop1_t)(d:nat) :=
match ls0 with
| nil => None
| h0::t0 =>
  let d := S d in
  let t1 := skipn d t0 in
  let t2 := skipn d t1 in
  let res := (expand_loop2 t0 t1 t2 [t1;t0] d (List.length t0)) in
  if (3 <=? List.length res)%nat then
  Some (map (@rev _) (map (firstn d) res))
  else find_loop2_0 t0 d
end.

Fixpoint preprocess''(x:list loop1_t)(y:int): _ :=
match x with
| [] => ([],y)
| (p,a,d,b)::x1 =>
  let p:=p-y in
  let a:=a+y in
  let '(y,b) :=
  (if Eqb.eqb b int0 then (int0,int0)
  else (d,b-int1))
  in
  let (x',y'):=preprocess'' x1 y in
  ((p,a,d,b)::x',y')
end.

Fixpoint preprocess'(x:list (list loop1_t))(y:int): _ :=
match x with
| [] => []
| x0::x1 =>
  let (x0,y):=preprocess'' x0 y in
  x0::preprocess' x1 y
end.

Definition preprocess'_v2(x:list (list loop1_t)) :=
map (map (fun '(p,a,d,b) =>
if Eqb.eqb b int0 then (p,a,d,b)
else (p,a+d,d,b-int1)
)) x.

Definition preprocess_v2 x :=
match x with
| [] => []
| x0::x1 =>
  preprocess'_v2 x1
end.

Fixpoint list_merge{T}(n:nat)(m:nat)(ls:list (list T)) :=
match m with
| O => []
| S m => (concat (firstn n ls)) :: list_merge n m (skipn n ls)
end.

Hypothesis n_merge:nat.
Definition preprocess_merge{T}(ls:list (list T)) :=
  let len := List.length ls in
  let ls := skipn (len mod n_merge) ls in
  list_merge n_merge (len/n_merge) ls.

Definition preprocess x :=
match x with
| [] => []
| x0::x1 =>
  let (_,y) := preprocess'' x0 int0 in
  preprocess_v2 (preprocess' x1 y)
end.

Definition preprocess_loop2 ls :=
match rev ls with
| ls0::ls1::_ =>
  (sub ls0 ls1) &&& (fun D =>
  Some (
  map (fun ls0 =>
    map (fun '((p,a,d,b),(_,_,_,db)) =>
      if eqb db int1 then (p,a,d,b)
      else if eqb db int0 then (p,a+d*b,int0,int0)
      else if int1<?db then (p,a+d*(b mod db),d*db,b/db)
      else (p,a,d,b)
    ) (combine ls0 D)
  ) ls))
| _ => None
end.

Definition find_loop1_as_loop2(ls:list loop1_t) :=
match ls with
| (p,a,d,b)::t =>
  let b := Z.to_nat (Uint63.to_Z b) in
  Some (rev (fst (Nat.iter b (fun '(x,y) => ([(y,d,int0,int0)]::x,y+d)) ([],p+a))))
| _ => None
end.

Hypothesis n_skip:nat.
Hypothesis loop1_as_loop2:bool.
Definition find_loop2 ls :=
  (if loop1_as_loop2 then find_loop1_as_loop2 ls else find_loop2_0 ls O) &&&
  (fun v => Some (preprocess_merge v)) &&&
  preprocess_loop2 &&&
  (fun v => Some ((Nat.iter n_skip preprocess v))).

Definition RelId:Type :=
  (int*(Box int)*(Box int)) +
  (int*(Box int)*int*(Box int)) +
  (Box int).

Definition pre_loop1(bid id1 id2:int):RelId :=
  inl (inl (bid,box id1,box id2)).

Definition in_loop1(bid id1 id2 id3:int):RelId :=
  inl (inr (bid,box id1,id2,box id3)).

Definition pre_loop2(id:int):RelId :=
  inr (box id).

Definition RelIdCtx:Type := list (list loop1_t).

Fixpoint get_RelId_1(x:int)(ls:list loop1_t)(bid id1:int):option RelId :=
match ls with
| nil => None
| (p,a,d,b)::t =>
  let p := Uint63.succ p in
  if x <? p then Some (pre_loop2 x)
  else
  if x <? p+a then Some (pre_loop1 bid id1 (x-p))
  else
  if x <? p+a+d*b then Some (in_loop1 bid id1 ((x-(p+a))/d) ((x-(p+a)) mod d))
  else
  get_RelId_1 x t bid (Uint63.succ id1)
end.

Fixpoint get_RelId_0(x:int)(ls:RelIdCtx)(bid:int):RelId :=
match ls with
| h::t =>
  match get_RelId_1 x h bid int0 with
  | None => get_RelId_0 x t (Uint63.succ bid)
  | Some v => v
  end
| nil => pre_loop2 x
end.

Section RelId_ctx.
Hypothesis ctx:RelIdCtx.

Definition get_RelId x :=
  get_RelId_0 x ctx int0.

Definition get_RelId' p :=
  info.[p] &&& (fun '(x,y,(z0,z1)) =>
  Some (x,y,(get_RelId z0,get_RelId z1))).

Definition eqb3{T}{x:Eqb T}(a b c:T):bool :=
  x.(eqb) a b && x.(eqb) b c.

Let len := Z.of_nat ((List.length ctx)-1).
Let len' := N.of_nat ((List.length ctx)-3).

Definition check_pre_loop1_at'(p0 p1 p2:int):=
  infox p0 &&& (fun v0 =>
  infox p1 &&& (fun v1 =>
  infox p2 &&& (fun v2 =>
  SegInterpolation.to_rule2_3 len' N0 v2 v1 v0 (1,0,0)%N (inl (N0,len'))))).
  
Definition check_in_loop1_at'(p00 p01 p02 p10 p11 p20:int)(loop_cnt_0 k:N):=
  infox p00 &&& (fun v00 =>
  infox p01 &&& (fun v01 =>
  infox p02 &&& (fun v02 =>
  infox p10 &&& (fun v10 =>
  infox p11 &&& (fun v11 =>
  infox p20 &&& (fun v20 =>
  SegInterpolation.to_rule2_6 (loop_cnt_0-1+len'-k) k v20 v11 v02 v10 v01 v00 (1,1,0)%N (inl (loop_cnt_0-1,loop_cnt_0-1+len')%N))))))).

Definition check_pre_loop1_at'dbg(p00 p01 p02:int):=
Some (check_pre_loop1_at' p00 p01 p02 ,(p00,p01,p02)).

Definition check_in_loop1_at'dbg(p00 p01 p02 p10 p11 p20:int)(loop_cnt_0 k:N):=
Some (check_in_loop1_at' p00 p01 p02 p10 p11 p20 loop_cnt_0 k,(p00,p01,p02,p10,p11,p20,loop_cnt_0,k)).

Definition chk_fixed'(p:int)(a b c:RelId):RelId*RelId*RelId :=
  if (eqb b (mul b Z0) && eqb b c)%bool then
  let w:=pre_loop2 p in
  (w,w,w)
  else (a,b,c).

Definition chk_fixed(p:int)(v dx dy:RelId*RelId):option (_*_*_) :=
  info.[p] &&& (fun '(_,(z0,z1)) =>
  let (v1,v2):=v in
  let (x1,x2):=dx in
  let (y1,y2):=dy in
  let '(v1,x1,y1):=chk_fixed' z0 v1 x1 y1 in
  let '(v2,x2,y2):=chk_fixed' z1 v2 x2 y2 in
  Some (((v1,v2)),((x1,x2)),((y1,y2)))).


Definition check_pre_loop1_at(p0 p1 p2:int):=
  get_RelId' p0 &&& (fun '(x0,y0,z0) =>
  get_RelId' p1 &&& (fun '(x1,y1,z1) =>
  get_RelId' p2 &&& (fun '(x2,y2,z2) =>
  sub z0 z1 &&& (fun dz =>
  if eqb (Some z2) (sub z1 dz) then
  chk_fixed p2 z2 dz dz &&& (fun '(z2,dz,_) =>
  SegInterpolation.to_4seg2_3 N0 N0 y2 y1 y0 &&& (fun y =>
  Some (p2,y,z2,dz)))
  else None
  ))))%bool.

Definition check_in_loop1_at(p00 p01 p02 p10 p11 p20:int)(loop_cnt_0 k:N):=
  get_RelId' p00 &&& (fun '(_,y00,z00) =>
  get_RelId' p01 &&& (fun '(_,y01,z01) =>
  get_RelId' p02 &&& (fun '(_,y02,z02) =>
  get_RelId' p10 &&& (fun '(_,y10,z10) =>
  get_RelId' p11 &&& (fun '(_,y11,z11) =>
  get_RelId' p20 &&& (fun '(_,y20,z20) =>
  sub z00 z01 &&& (fun dy =>
  sub z00 z10 &&& (fun dx =>
  if 
  eqb (Some z02) ((sub z01 dy)) &&
  eqb3 (Some z11) ((sub z01 dx)) ((sub z10 dy)) &&
  eqb (Some z20) ((sub z10 dx))
  then
  let dy:=mul dy (-1)%Z in
  chk_fixed p20 z20 dx dy &&& (fun '(z20,dx,dy) =>
  SegInterpolation.to_4seg2_6 N0 N0 y20 y11 y02  y10 y01  y00 &&& (fun y =>
  Some (p20,y,z20,dx,dy)))
  else None
  ))))))))%bool.

Definition check_pre_loop1_at_dbg(p0 p1 p2:int):=
Some (p0,p1,p2,check_pre_loop1_at p0 p1 p2).

Definition check_in_loop1_at_dbg(p00 p01 p02 p10 p11 p20:int)(l k:N):=
Some (p00,p01,p02,p10,p11,p20,check_in_loop1_at p00 p01 p02 p10 p11 p20 l k).

Hypothesis k:int.

Fixpoint int_range_omap_0{T}(f:int->option T)(n:int)(n0:nat):option (list T) :=
match n0 with
| O => Some nil
| S n1 =>
  f n &&& (fun v =>
  int_range_omap_0 f (n-int1) n1 &&& (fun v' =>
  Some (v::v')))
end.

Definition int_range_omap{T}(f:int->option T)(n:int):option (list T) :=
let n0 := Z.to_nat (Uint63.to_Z n) in
int_range_omap_0 f n n0 &&& (fun v => Some (rev v)).

Definition check_loop2_1'(x0 x1 x2:loop1_t) :=
let '(p0,a0,d0,b0) := x0 in
let '(p1,_,_,b1) := x1 in
let '(p2,_,_,b2) := x2 in
let n1 := a0+d0*k in
let loop_cnt_0 :=(Z.to_N ((Uint63.to_Z b0)-len)) in
if ((k <? b2))%bool then
(
int_range_omap (fun n => (check_in_loop1_at  (p0+n1+n) (p0+n1+d0+n) (p0+n1+d0+d0+n) (p1+n1+n) (p1+n1+d0+n) (p2+n1+n) loop_cnt_0 (to_N k))) (d0) &&& (fun v3 =>
int_range_omap (fun n => (check_in_loop1_at' (p0+n1+n) (p0+n1+d0+n) (p0+n1+d0+d0+n) (p1+n1+n) (p1+n1+d0+n) (p2+n1+n) loop_cnt_0 (to_N k))) (d0) &&& (fun v3' =>
int_range_omap (fun n => (check_pre_loop1_at (p0+n) (p1+n) (p2+n))) n1 &&& (fun v1 =>
int_range_omap (fun n => (check_pre_loop1_at (p0+n1+d0*int3+n) (p1+n1+d0*int2+n) (p2+n1+d0*int1+n))) (d0*(b2-int1-k)) &&& (fun v2 =>
int_range_omap (fun n => (check_pre_loop1_at' (p0+n) (p1+n) (p2+n))) a0 &&& (fun v1' =>
Some ((v1',v3'),(v1,v2,v3,k,(b2-int1-k)))
   )))))
   )
else if eqb b2 int0 then
(
int_range_omap (fun n => (check_pre_loop1_at (p0+n) (p1+n) (p2+n))) a0 &&& (fun v1 =>
int_range_omap (fun n => (check_pre_loop1_at' (p0+n) (p1+n) (p2+n))) a0 &&& (fun v1' =>
Some ((v1',[]),(v1,[],[],int0,int0))
   ))
   )
else None
.

Definition F{A B}(x:list (A*(option B))) :=
filter (fun x =>
match snd x with
| Some _ => false
| _ => true
end) x.

Definition check_loop2_1'dbg(x0 x1 x2:loop1_t) :=
let '(p0,a0,d0,b0) := x0 in
let '(p1,_,_,b1) := x1 in
let '(p2,_,_,b2) := x2 in
let n1 := a0+d0*k in
let loop_cnt_0 :=(Z.to_N ((Uint63.to_Z b0)-len)) in
if ((k <? b2))%bool then
(
int_range_omap (fun n => (check_in_loop1_at_dbg (p0+n1+n) (p0+n1+d0+n) (p0+n1+d0+d0+n) (p1+n1+n) (p1+n1+d0+n) (p2+n1+n) loop_cnt_0 (to_N k))) (d0) &&& (fun v3 =>
int_range_omap (fun n => (check_in_loop1_at'dbg (p0+n1+n) (p0+n1+d0+n) (p0+n1+d0+d0+n) (p1+n1+n) (p1+n1+d0+n) (p2+n1+n) loop_cnt_0 (to_N k))) (d0) &&& (fun v3' =>
int_range_omap (fun n => (check_pre_loop1_at_dbg (p0+n) (p1+n) (p2+n))) n1 &&& (fun v1 =>
int_range_omap (fun n => (check_pre_loop1_at_dbg (p0+n1+d0*int3+n) (p1+n1+d0*int2+n) (p2+n1+d0*int1+n))) (d0*(b2-int1-k)) &&& (fun v2 =>
int_range_omap (fun n => (check_pre_loop1_at'dbg (p0+n) (p1+n) (p2+n))) a0 &&& (fun v1' =>
Some ((v1',v3'),(F v1,F v2,F v3,k,(b2-int1-k)))
   )))))
   )
else if eqb b2 int0 then
(
int_range_omap (fun n => (check_pre_loop1_at_dbg (p0+n) (p1+n) (p2+n))) a0 &&& (fun v1 =>
int_range_omap (fun n => (check_pre_loop1_at'dbg (p0+n) (p1+n) (p2+n))) a0 &&& (fun v1' =>
Some ((v1',[]),(F v1,[],[],int0,int0))
   ))
   )
else None
.


Fixpoint check_loop2_0'(ls0 ls1 ls2:list loop1_t) :=
match ls0,ls1,ls2 with
| h0::t0,h1::t1,h2::t2 =>
  check_loop2_1' h0 h1 h2 &&& (fun v =>
  check_loop2_0' t0 t1 t2 &&& (fun v' =>
  Some (v::v')))
| nil,nil,nil => Some nil
| _,_,_ => None
end.

Fixpoint check_loop2_0'dbg(ls0 ls1 ls2:list loop1_t) :=
match ls0,ls1,ls2 with
| h0::t0,h1::t1,h2::t2 =>
  check_loop2_1'dbg h0 h1 h2 &&& (fun v =>
  check_loop2_0'dbg t0 t1 t2 &&& (fun v' =>
  Some (v::v')))
| nil,nil,nil => Some nil
| _,_,_ => None
end.

Definition check_loop2' :=
match rev ctx with
| ls0::ls1::ls2::_ =>
  check_loop2_0' ls0 ls1 ls2
| _ => None
end.

Definition check_loop2'dbg :=
match rev ctx with
| ls0::ls1::ls2::_ =>
  check_loop2_0'dbg ls0 ls1 ls2
| _ => None
end.

(*
Definition to_seg1'(x:seg) :=
  snd (to_seg1xy 4 x).
Definition to_config1(x:Config0.T) :=
let '(l,r,s,sgn) := x in (to_seg1' l,to_seg1' r,s,sgn).
Definition to_rule1(x:Rule0.T) :=
let '(x0,x1):=x in (to_config1 x0,to_config1 x1).
Definition show_loop1(x0:loop1_t) :=
let '(p0,a0,d0,b0) := x0 in
int_range_omap (fun n => (Rule0IdAlloc.get_key (p0+a0+n) st.(rule0_id)) &&& (fun v => Some (to_rule1 v))) (d0*b0)
.*)

Section solve_ctx.
Hypothesis H H':rule4.
Hypothesis H_ind:rule4.

Definition solve_rule0(x:Rule0.T):bool :=
o2b (Rule0IdAlloc.get_id x st.(rule0_id)).

Definition config2_no_var(x:config2):bool :=
eqb (config2_subst N3_0 N3_0 x) x.

Definition rule2_no_var(x:rule2):bool :=
let '(c1,c2,c3,c4):=x in
(eqb (c3,c4) (0,0,0,inl (0,1))%N &&
config2_no_var c1 &&
config2_no_var c2)%bool.

Definition solve_rule2_O(x:rule2):bool :=
(rule2_no_var x &&
o2b (rule2_to_list_rule0 MAXT x &&& (fun v => b2o (forallb solve_rule0 v))))%bool.


Fixpoint int_nth{A}(n:int)(ls:list A):option A :=
match ls with
| h::t =>
  if eqb n int0 then Some h
  else int_nth (n-int1) t
| _ => None
end.

Definition get_rule2_from(x:rule4)(i:int*int+int*int):option rule2 :=
match i with
| inl (a,b) =>
  int_nth a x &&& (fun '(x,_) =>
  int_nth b x)
| inr (a,b) =>
  int_nth a x &&& (fun '(_,x) =>
  int_nth b x)
end.

Definition get_loop_cnt(a b:int):option int :=
  int_nth a ctx &&& (fun ctx1 =>
  int_nth b ctx1 &&& (fun '(_,_,_,b') => Some b')).


Definition seg0to2(x:seg):seg2 :=
  map (fun a => ([a],N3_1)) x.

Definition config0to2(x:Config0.T):config2 :=
let '(l,r,s,sgn):=x in
(seg0to2 l,seg0to2 r,s,sgn).

Definition rule0to2(x:Rule0.T):rule2 :=
let (x0,x1):=x in
(config0to2 x0,config0to2 x1,N3_0,inl (0,1)%N).


Definition get_rule2_from_rule0(p:int):option rule2 :=
  Rule0IdAlloc.get_key p rid &&& (fun w0 =>
  let w:=rule0to2 w0 in
  if (solve_rule2_O w) then Some w
  else None
  ).

Definition RelId_ab(p':RelId):option _ :=
match p' with
| inl (inl (a,box b,box c)) => Some (a,b,inl c)
| inl (inr (a,box b,c,box d)) => Some (a,b,inr (c,d))
| _ => None
end.

Definition get_rule2(p' z dz:RelId):option rule2 :=
RelId_ab p' &&& (fun '(pa,pb,pcd) =>
match z,dz with
| inl (inl (a,box b,box c)),inl (inl (da,_,_)) =>
  if eqb a pa then
    get_rule2_from H' (inl (b,c)) &&& (fun w =>
    if eqb da int1 then
      Some w
    else None)
  else if a<?pa then
    get_rule2_from H (inl (b,c)) &&& (fun w =>
    if eqb da int1 then
      let x:=to_N ((pa-a-int1)) in
      rule2_lt_to_eq w x
    else None)
  else None
| inl (inr (a,box b,c,box d)),inl (inr (da,_,dc,_)) =>
  if eqb a pa then
    if eqb b pb then
      match pcd with
      | inr (pc,pd) =>
        get_rule2_from H_ind (inl (pc-c,d)) ||| (
        get_rule2_from H' (inr (b,d)) &&& (fun w =>
        if eqb (da,dc) (int1,int0) then
          let y:=to_N (c) in
          Some (rule2_subst (1,0,0) (0,0,y) w)%N
        else if eqb (da,dc) (int1,int1) then
          (let b':=k+int1 in
          let y:=to_N ((b'-c-int1)) in
          Some (rule2_subst (0,0,y) (1,0,0) w)%N)
        else None))
      | _ => None
      end
    else
      get_rule2_from H' (inr (b,d)) &&& (fun w =>
      if eqb (da,dc) (int1,int0) then
        let y:=to_N (c) in
        Some (rule2_subst (1,0,0) (0,0,y) w)%N
      else if eqb (da,dc) (int1,int1) then
        get_loop_cnt a b &&& (fun b' =>
        let y:=to_N ((b'-c-int1)) in
        Some (rule2_subst (0,0,y) (1,0,0) w)%N)
      else None)
  else if a<?pa then
    get_rule2_from H (inr (b,d)) &&& (fun w =>
    if eqb (da,dc) (int1,int0) then
      let x:=to_N ((pa-a-int1)) in
      let y:=to_N (c) in
      rule2_lt_to_eq w x &&& (fun w =>
      Some (rule2_subst (1,0,0) (0,0,y) w)%N)
    else if eqb (da,dc) (int1,int1) then
      get_loop_cnt a b &&& (fun b' =>
      let x:=to_N ((pa-a-int1)) in
      let y:=to_N ((b'-c-int1)) in
      rule2_lt_to_eq w x &&& (fun w =>
      Some (rule2_subst (0,0,y) (1,0,0) w)%N))
    else None)
  else None
| inr (box p),_ =>
  get_rule2_from_rule0 p
| _,_ => None
end).

Definition get_rule2'(p' z z0 z1:RelId):option rule2 :=
match p' with
| inl (inr (pa,box pb,pc,box pd)) =>
match z,z0,z1 with
| inl (inl (a,box b,box c)),
  inl (inl (a0,_,_)),
  inl (inl (a1,_,_)) =>
  get_rule2_from H (inl (b,c)) &&& (fun w =>
  if eqb (a0,a1) (int0,int1) then
    rule2_lt_to_eq' w &&& (fun w =>
    let y0:=to_N a in
    let y1:=to_N (pa-a-int1) in
    Some (rule2_subst (0,1,y0) (1,0,y1) w)%N)
  else if eqb (a0,a1) (int1,neg1) then
    rule2_lt_to_eq' w &&& (fun w =>
    let y0:=to_N a in
    let y1:=to_N (pa-a-int1) in
    Some (rule2_subst (1,0,y0) (0,1,y1) w)%N)
  else None)
| inl (inr (a,box b,c,box d)),
  inl (inr (a0,_,c0,_)),
  inl (inr (a1,_,c1,_)) =>
  if eqb a pa then
    if eqb b pb then
      if eqb ((a0,c0),(a1,c1)) ((int1,int0),(int0,int1)) then
        get_rule2_from H_ind (inl (pc-c,d))
      else None
    else if b<?pb then
      get_rule2_from H' (inr (b,d)) &&& (fun w =>
      if eqb ((a0,c0),(a1,c1)) ((int1,int0),(int0,int1)) then
        get_loop_cnt a b &&& (fun b' =>
        let y0:=to_N ((b'-c-int1)) in
        let y1:=to_N ((c)) in
        Some (rule2_subst (1,0,y0) (0,1,y1) w)%N)
      else if eqb ((a0,c0),(a1,c1)) ((int1,int1),(int0,neg1)) then
        get_loop_cnt a b &&& (fun b' =>
        let y0:=to_N ((b'-c-int1)) in
        let y1:=to_N ((c)) in
        Some (rule2_subst (0,1,y0) (1,0,y1) w)%N)
      else None)
    else None
  else if a<?pa then
    get_rule2_from H (inr (b,d)) &&& (fun w =>
    if eqb ((a0,c0),(a1,c1)) ((int1,int0),(int0,int1)) then
      get_loop_cnt a b &&& (fun b' =>
      let x:=to_N ((pa-a-int1)) in
      let y0:=to_N ((b'-c-int1)) in
      let y1:=to_N ((c)) in
      rule2_lt_to_eq w x &&& (fun w =>
      Some (rule2_subst (1,0,y0) (0,1,y1) w)%N))
    else if eqb ((a0,c0),(a1,c1)) ((int1,int1),(int0,neg1)) then
      get_loop_cnt a b &&& (fun b' =>
      let x:=to_N ((pa-a-int1)) in
      let y0:=to_N ((b'-c-int1)) in
      let y1:=to_N ((c)) in
      rule2_lt_to_eq w x &&& (fun w =>
      Some (rule2_subst (0,1,y0) (1,0,y1) w)%N))
    else None)
  else None
| inr (box p),_,_ =>
  get_rule2_from_rule0 p
| _,_,_ => None
end
| _ => None
end.


Definition verify_imp(H G:N3*(N*N+N)):bool :=
(eqb H G || eqb G (N3_0,inl (0,1)%N))%bool.

Definition verify_rule2(G13 G12 G23:rule2):option unit :=
let '(c1,c2,c3,c4):=G13 in
let '(c1a,c2a,c3a,c4a):=G12 in
let '(c1b,c2b,c3b,c4b):=G23 in
if (verify_imp (c3,c4) (c3a,c4a) && verify_imp (c3,c4) (c3b,c4b) && solve_config2_eq c1 c1a && solve_config2_eq c2a c1b && solve_config2_eq c2b c2)%bool then
Some tt
else None.

Definition verify_rule2'(G13 G12 G23:rule2):option unit :=
  verify_rule2
  (rule2_eq_r_simpl G13)
  (rule2_eq_r_simpl G12)
  (rule2_eq_r_simpl G23).

Definition solve_pre_loop1_at(hint:int*(seg2*seg2*seg2*seg2)*(RelId*RelId)*(RelId*RelId))(G:rule2):option unit :=
let '(p,(l1,r1,l2,r2),(z0,z1),(dz0,dz1)):=hint in
  let p':=get_RelId p in
  get_rule2 p' z0 dz0 &&& (fun G12 =>
  get_rule2 p' z1 dz1 &&& (fun G23 =>
  verify_rule2 (rule2_eq_r_simpl G)
    (rule2_subst2 (rule2_eq_r_simpl G12) l1 r1)
    (rule2_subst1 (rule2_eq_r_simpl G23) l2 r2)
  )).

Definition solve_in_loop1_at(hint:int*(seg2*seg2*seg2*seg2)*(RelId*RelId)*(RelId*RelId)*(RelId*RelId))(G:rule2):option unit :=
let '(p,(l1,r1,l2,r2),(z0,z1),(z00,z10),(z01,z11)):=hint in
  let p':=get_RelId p in
  get_rule2' p' z0 z00 z01 &&& (fun G12 =>
  get_rule2' p' z1 z10 z11 &&& (fun G23 =>
  verify_rule2 G
    (rule2_subst2 G12 l1 r1)
    (rule2_subst1 G23 l2 r2)
  )).

End solve_ctx.


Hypothesis tm:TM.

Hypothesis H_rid:
  forall x,
  match Rule0IdAlloc.get_id x rid with
  | Some _ => Rule0.to_prop x tm
  | _ => True
  end.

Section C_ctx.
Hypothesis C:N.
Lemma solve_rule0_spec x:
if solve_rule0 x then Rule0.to_prop x tm else True.
Proof.
  unfold solve_rule0.
  pose proof (H_rid x) as H_rid.
  unfold rid in H_rid.
  destruct (Rule0IdAlloc.get_id x (rule0_id st)); cbn; trivial.
Qed.

Definition solve_rule4_O(x:rule4):option unit :=
let x:=rule4_to_list_rule2 x in
list_rule2_to_list_rule0 x &&& (fun x =>
b2o (forallb solve_rule0 x)).

Lemma solve_rule4_O_spec x:
match solve_rule4_O x with
| Some _ => rule4_to_prop tm N0 x
| _ => True
end.
Proof.
  unfold solve_rule4_O.
  unfold if_Some.
  destruct_spec (list_rule2_to_list_rule0_spec tm); trivial.
  pose proof (rule4_to_list_rule2_spec tm N0 x) as H0.
  pose proof (forallb_forall solve_rule0 l) as H1.
  unfold b2o.
  destruct_spec forallb; trivial.
  rewrite H0.
  apply H.
  destruct H1 as [H1 _].
  specialize (H1 eq_refl).
  rewrite Forall_forall.
  intros x0 Hx0.
  specialize (H1 x0 Hx0).
  pose proof (solve_rule0_spec x0) as H3.
  rewrite H1 in H3.
  apply H3.
Qed.

Definition rule4_new(x:nat):rule4 :=
repeat (([],[])) x.

Definition rule4_push0(x:rule4):rule4 := ([],[])::x.

Fixpoint solve_pre_loop1(H H':rule4)(G:rule2ls) h a:option (rule4*_) :=
match G,h with
| [],_ => Some (H',h)
| G0::G,h0::h =>
  solve_pre_loop1_at H H' [] h0 G0 &&& (fun _ =>
  solve_pre_loop1 H (rule4_add H' a G0) G h a)
| _,_ => None
end.

Fixpoint solve_in_loop1_pre_0(H H' H_ind:rule4)(G:rule2ls) h:option (rule4*_) :=
match G,h with
| [],_ => Some (H_ind,h)
| G0::G,h0::h =>
  solve_pre_loop1_at H H' H_ind h0 G0 &&& (fun _ =>
  solve_in_loop1_pre_0 H H' (rule4_add H_ind int0 G0) G h)
| _,_ => None
end.

Fixpoint solve_in_loop1_pre(H H' H_ind G:rule4) h:option unit :=
match G with
| [] => Some tt
| (G0,[])::G =>
  solve_in_loop1_pre_0 H H' (rule4_push0 H_ind) G0 h &&& (fun '(H_ind,h) =>
  solve_in_loop1_pre H H' H_ind G h)
| _ => None
end.

Fixpoint solve_in_loop1(H H' H_ind:rule4)(G:rule2ls) h:option unit :=
match G,h with
| [],_ => Some tt
| G0::G,h0::h =>
  solve_in_loop1_at H H' H_ind h0 G0 &&& (fun _ =>
  solve_in_loop1 H H' (rule4_add H_ind int0 G0) G h)
| _,_ => None
end.

Definition list_rule3_to_rule4(x:list rule3):rule4 :=
List.map (fun a => (rule3_to_list_rule2 a,[])) x.

Fixpoint solve_rule4_0(H H' G:rule4) h a{struct G}:option unit :=
match G,h with
| [],_ => Some tt
| (G0,G1)::G,(h1,h2,h3,k0,k1)::h =>
  solve_pre_loop1 H H' G0 h1 a &&& (fun '(H',h1') =>
  if eqb G1 [] then
  solve_rule4_0 H H' G h (a+int1)
  else
  list_rule2_ind G1 ((to_N k0)-1)%N (to_N k1) &&& (fun '(IG0,(IH,IG),IG1,IX1) =>
  solve_in_loop1_pre H H' [] IG0 h1' &&& (fun _ =>
  solve_in_loop1_pre H (rule4_upd H' a IX1) [] (rev IG1) h2 &&& (fun _ =>
  let IH:=list_rule3_to_rule4 (rev IH) in
  let IG:=rule3_to_list_rule2 IG in
  solve_in_loop1 H H' (rule4_push0 IH) IG h3 &&& (fun _ =>
  solve_rule4_0 H (rule4_upd H' a G1) G h (a+int1))))))
| _,_ => None
end.

Definition solve_rule4(G0:rule4) h:option unit :=
solve_rule4_O G0 &&& (fun _ =>
let (H,G):=(G0,subst_rule4_Sc G0) in
(rule4_lt_r_S H G) &&& (fun G' =>
solve_rule4_0 H (rule4_new (List.length G')) G' h int0)).


Lemma rule4_add_spec x i y:
  rule4_to_prop tm C x ->
  rule2_to_prop tm C y ->
  rule4_to_prop tm C (rule4_add x i y).
Proof.
  gen i.
  induction x as [|[x0 x1] x]; intros.
  - cbn; trivial.
  - cbn - [eqb].
    unfold rule4_to_prop in *.
    destruct (eqb i int0); simpl_Forall.
    + unfold pair_list_rule2_to_prop in *.
      unfold list_rule2_to_prop in *.
      simpl_Forall.
      tauto.
    + intuition.
Qed.

Hypothesis H_rid_WF:
  Rule0IdAlloc.id_alloc_WF rid.

Lemma config2_no_var_spec x:
if config2_no_var x then
  (forall i0 i1,
  config2_csubst N0 N0 x =
  config2_csubst i0 i1 x)
else True.
Proof.
  unfold config2_no_var.
  destruct (eqb_spec (config2_subst N3_0 N3_0 x) x); trivial.
  intros.
  rewrite <-e.
  repeat rewrite (config2_subst_spec).
  reflexivity.
Qed.

Lemma rule2_no_var_spec x:
if rule2_no_var x then
  rule2_to_pred tm N0 x N0 N0 ->
  rule2_to_prop tm C x
else True.
Proof.
  unfold rule2_no_var.
  destruct x as [[[c1 c2] c3] c4].
  destruct (eqb_spec (c3,c4) (0,0,0,inl (0,1)))%N; trivial.
  destruct_spec config2_no_var_spec; trivial.
  destruct_spec config2_no_var_spec; trivial.
  unfold rule2_to_prop.
  unfold rule2_to_pred.
  intros.
  rewrite <-H,<-H0.
  apply H1.
  inverts e.
  cbn. lia.
Qed.

Lemma solve_rule2_O_spec x:
match solve_rule2_O x with
| true => rule2_to_prop tm C x
| _ => True
end.
Proof.
  unfold solve_rule2_O.
  unfold if_Some,o2b,b2o.
  destruct_spec rule2_no_var_spec. 2: trivial.
  destruct_spec (rule2_to_list_rule0_spec tm); trivial.
  destruct (forallb solve_rule0 l) eqn:E; trivial.
  rewrite Forall_forall in H0.
  rewrite forallb_forall in E.
  apply H.
  unfold rule2_to_prop in H0.
  apply H0.
  intros.
  specialize (E _ H1).
  pose proof (solve_rule0_spec x0) as H2.
  rewrite E in H2.
  apply H2.
Qed.

Lemma get_rule2_from_rule0_spec p:
match get_rule2_from_rule0 p with
| None => True
| Some w =>
  rule2_to_prop tm C w
end.
Proof.
  unfold get_rule2_from_rule0,if_Some.
  destruct (Rule0IdAlloc.get_key p rid) eqn:E. 2: trivial.
  destruct_spec solve_rule2_O_spec; trivial.
Qed.

Lemma int_nth_spec {T} a (x:list T):
match int_nth a x with
| None => True
| Some y => In y x
end.
Proof.
  gen a.
  induction x; intros; cbn - [eqb]; trivial.
  destruct (eqb a0 int0).
  - tauto.
  - specialize (IHx (a0-int1)).
    destruct (int_nth (a0-int1) x); trivial.
    tauto.
Qed.


Lemma get_rule2_from_spec H x:
match get_rule2_from H x with
| None =>True
| Some w =>
  rule4_to_prop tm C H ->
  rule2_to_prop tm C w
end.
Proof.
  unfold get_rule2_from,if_Some.
  destruct x as [[a b]|[a b]].
  - pose proof (int_nth_spec a H) as Ha.
    destruct (int_nth a H) as [[x0 x1]|]; trivial.
    pose proof (int_nth_spec b x0) as Hb.
    destruct (int_nth b x0) as [w|]; trivial.
    unfold rule4_to_prop,pair_list_rule2_to_prop,list_rule2_to_prop.
    intros X.
    rewrite Forall_forall in X.
    specialize (X _ Ha); cbn in X.
    destruct X as [X _].
    rewrite Forall_forall in X.
    apply X; tauto.
  - pose proof (int_nth_spec a H) as Ha.
    destruct (int_nth a H) as [[x1 x0]|]; trivial.
    pose proof (int_nth_spec b x0) as Hb.
    destruct (int_nth b x0) as [w|]; trivial.
    unfold rule4_to_prop,pair_list_rule2_to_prop,list_rule2_to_prop.
    intros X.
    rewrite Forall_forall in X.
    specialize (X _ Ha); cbn in X.
    destruct X as [_ X].
    rewrite Forall_forall in X.
    apply X; tauto.
Qed.

Definition list_rule2_to_pred(x:rule2ls)(i0 i1:N):Prop :=
Forall (fun a => rule2_to_pred tm C a i0 i1) x.

Definition pair_list_rule2_to_pred(x:rule2ls*rule2ls)(i0 i1:N):Prop :=
let (x0,x1):=x in
list_rule2_to_pred x0 i0 i1 /\
list_rule2_to_pred x1 i0 i1.

Definition rule4_to_pred(x:rule4)(i0 i1:N):Prop :=
Forall (fun x => pair_list_rule2_to_pred x i0 i1) x.

Lemma get_rule2_from_spec' H x:
match get_rule2_from H x with
| None =>True
| Some w =>
  forall i0 i1,
  rule4_to_pred H i0 i1 ->
  rule2_to_pred tm C w i0 i1
end.
Proof.
  unfold get_rule2_from,if_Some.
  destruct x as [[a b]|[a b]].
  - pose proof (int_nth_spec a H) as Ha.
    destruct (int_nth a H) as [[x0 x1]|]; trivial.
    pose proof (int_nth_spec b x0) as Hb.
    destruct (int_nth b x0) as [w|]; trivial.
    unfold rule4_to_pred,pair_list_rule2_to_pred,list_rule2_to_pred.
    intros i0 i1 X.
    rewrite Forall_forall in X.
    specialize (X _ Ha); cbn in X.
    destruct X as [X _].
    rewrite Forall_forall in X.
    apply X; tauto.
  - pose proof (int_nth_spec a H) as Ha.
    destruct (int_nth a H) as [[x1 x0]|]; trivial.
    pose proof (int_nth_spec b x0) as Hb.
    destruct (int_nth b x0) as [w|]; trivial.
    unfold rule4_to_pred,pair_list_rule2_to_pred,list_rule2_to_pred.
    intros i0 i1 X.
    rewrite Forall_forall in X.
    specialize (X _ Ha); cbn in X.
    destruct X as [_ X].
    rewrite Forall_forall in X.
    apply X; tauto.
Qed.

Lemma rule2_subst_spec' i0' i1' x:
  rule2_to_prop tm C x ->
  rule2_to_prop tm C (rule2_subst i0' i1' x).
Proof.
  unfold rule2_to_prop.
  intros.
  rewrite rule2_subst_spec.
  apply H.
Qed.

Lemma get_rule2_spec H H' H_ind p' z dz:
match get_rule2 H H' H_ind p' z dz with
| None => True
| Some w =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  rule4_to_prop tm C H_ind ->
  rule2_to_prop tm C w
end.
Proof with trivial.
  unfold get_rule2,if_Some.
  destruct (RelId_ab p') as [[[pa pb] pcd]|]...
  destruct z as [[z|z]|z].
  - destruct z as [[a [b]] [c]].
    destruct dz as [[dz|dz]|dz]...
    destruct dz as [[da _] _].
    destruct (eqb_spec a pa).
    + destruct_spec get_rule2_from_spec...
      destruct (eqb da int1)...
      tauto.
    + destruct (a<?pa)...
      destruct_spec get_rule2_from_spec...
      destruct (eqb da int1)...
      destruct_spec (rule2_lt_to_eq_spec)...
      unfold rule2_to_prop.
      intuition.
  - destruct z as [[[a [b]] c] [d]].
    destruct dz as [[dz|dz]|dz]...
    destruct dz as [[[da _] dc] _].
    destruct (eqb a pa).
    + destruct (eqb b pb).
      * destruct pcd as [|[pc _]]...
        destruct_spec get_rule2_from_spec.
        -- tauto.
        -- destruct_spec get_rule2_from_spec...
           destruct (eqb (da,dc) (int1,int0)).
           ++ intros.
              apply rule2_subst_spec'.
              tauto.
           ++ intros.
              destruct (eqb (da,dc) (int1,int1)).
              ** intros.
                 apply rule2_subst_spec'.
                 tauto.
              ** tauto.
      * destruct_spec get_rule2_from_spec...
         destruct (eqb (da,dc) (int1,int0)).
         ++ intros.
            apply rule2_subst_spec'.
            tauto.
         ++ intros.
            destruct (eqb (da,dc) (int1,int1)).
            ** destruct_spec get_loop_cnt...
               intros.
               apply rule2_subst_spec'.
               tauto.
            ** tauto.
    + destruct (a<?pa)...
      destruct_spec get_rule2_from_spec...
       destruct (eqb (da,dc) (int1,int0)).
       ++ destruct_spec rule2_lt_to_eq_spec...
          intros.
          apply rule2_subst_spec'.
          intros i0 i1.
          intuition.
       ++ intros.
          destruct (eqb (da,dc) (int1,int1)).
          ** destruct_spec get_loop_cnt...
             destruct_spec rule2_lt_to_eq_spec...
             intros.
             apply rule2_subst_spec'.
             intros i0 i1.
             intuition.
          ** tauto.
  - destruct z as [z].
    destruct_spec get_rule2_from_rule0_spec...
Qed.


Lemma verify_imp_spec c3 c4 c3' c4':
if verify_imp (c3,c4) (c3',c4') then
  forall i0 i1,
  match c4 with
  | inl (l, r) => (l <= N3dot c3 (i0, i1, 1) < r + C)%N
  | inr v => N3dot c3 (i0, i1, 1%N) = (v + C)%N
  end ->
  match c4' with
  | inl (l, r) => (l <= N3dot c3' (i0, i1, 1) < r + C)%N
  | inr v => N3dot c3' (i0, i1, 1%N) = (v + C)%N
  end
else True.
Proof.
  unfold verify_imp.
  destruct (eqb_spec (c3,c4) (c3',c4')).
  - inverts e; intros; tauto.
  - destruct (eqb_spec (c3',c4') (0,0,0,inl (0,1))%N); trivial.
    inverts e; intros.
    unfold N3dot.
    lia.
Qed.

Lemma verify_rule2_spec G13 G12 G23:
match verify_rule2 G13 G12 G23 with
| None => True
| Some _ =>
  forall i0 i1,
  rule2_to_pred tm C G12 i0 i1 ->
  rule2_to_pred tm C G23 i0 i1 ->
  rule2_to_pred tm C G13 i0 i1
end.
Proof with trivial.
  unfold verify_rule2.
  refine (
  let '(c1,c2,c3,c4):=G13 in
  let '(c1a,c2a,c3a,c4a):=G12 in
  let '(c1b,c2b,c3b,c4b):=G23 in
  _).
  pose proof (verify_imp_spec c3 c4 c3a c4a).
  pose proof (verify_imp_spec c3 c4 c3b c4b).
  destruct_spec verify_imp...
  destruct_spec verify_imp...
  destruct_spec (solve_config2_eq_spec)...
  destruct_spec (solve_config2_eq_spec)...
  destruct_spec (solve_config2_eq_spec)...
  intros.
  specialize (H3 i0 i1).
  specialize (H4 i0 i1).
  specialize (H5 i0 i1).
  specialize (H i0 i1).
  specialize (H0 i0 i1).
  unfold rule2_to_pred in *.
  rewrite H3 in *.
  rewrite H4 in *.
  rewrite H5 in *.
  unfold Rule0.to_prop in *.
  intros.
  eapply evstep_trans.
  - apply H6.
    tauto.
  - apply H7.
    tauto.
Qed.

Lemma verify_rule2'_spec G13 G12 G23:
match verify_rule2' G13 G12 G23 with
| None => True
| Some _ =>
  rule2_to_prop tm C G12 ->
  rule2_to_prop tm C G23 ->
  rule2_to_prop tm C G13
end.
Proof.
  unfold verify_rule2'.
  destruct_spec verify_rule2_spec; trivial.
  pose proof (rule2_eq_r_simpl_spec) as R.
  unfold rule2_to_prop in *.
  rewrite (R G13),(R G23),(R G12).
  intuition.
Qed.

Lemma solve_pre_loop1_at_spec H H' H_ind h w:
match solve_pre_loop1_at H H' H_ind h w with
| None => True
| Some _ =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  rule4_to_prop tm C H_ind ->
  rule2_to_prop tm C w
end.
Proof.
  unfold solve_pre_loop1_at.
  unfold if_Some.
  refine (let '(p,(l1,r1,l2,r2),(z0,z1),(dz0,dz1)):=h in _).
  destruct_spec (get_rule2_spec); trivial.
  destruct_spec (get_rule2_spec); trivial.
  destruct_spec (verify_rule2_spec); trivial.
  intros.
  pose proof rule2_eq_r_simpl_spec as He.
  unfold rule2_to_prop in *.
  rewrite He.
  intros.
  apply H2.
  - apply rule2_subst2_spec.
    gen i0 i1.
    rewrite <-He.
    intuition.
  - apply rule2_subst1_spec.
    gen i0 i1.
    rewrite <-He.
    intuition.
Qed.

Lemma solve_pre_loop1_spec H H' G h a:
match solve_pre_loop1 H H' G h a with
| None => True
| Some (H'',h') =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  (rule4_to_prop tm C H'' /\
  list_rule2_to_prop tm C G)
end.
Proof.
  gen H' h.
  induction G as [|G0 G]; intros.
  - cbn.
    unfold list_rule2_to_prop in *.
    simpl_Forall.
    tauto.
  - cbn.
    destruct h as [|h0 h]; trivial.
    unfold if_Some.
    destruct_spec (solve_pre_loop1_at_spec); trivial.
    specialize (IHG (rule4_add H' a G0) h).
    destruct_spec solve_pre_loop1; trivial.
    destruct p as [H'' h'].
    pose proof (rule4_add_spec H' a G0) as Ha.
    unfold list_rule2_to_prop in *.
    unfold rule4_to_prop in *.
    simpl_Forall.
    tauto.
Qed.

Lemma solve_in_loop1_pre_0_spec H H' H_ind G h:
match solve_in_loop1_pre_0 H H' H_ind G h with
| None => True
| Some (H'',h') =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  rule4_to_prop tm C H_ind ->
  (rule4_to_prop tm C H'' /\
  list_rule2_to_prop tm C G)
end.
Proof.
  gen H_ind h.
  induction G as [|G0 G]; intros.
  - cbn.
    unfold list_rule2_to_prop in *.
    simpl_Forall.
    tauto.
  - cbn.
    destruct h as [|h0 h]; trivial.
    unfold if_Some.
    destruct_spec (solve_pre_loop1_at_spec); trivial.
    specialize (IHG (rule4_add H_ind int0 G0) h).
    destruct_spec solve_in_loop1_pre_0; trivial.
    destruct p as [H'' h'].
    pose proof (rule4_add_spec H_ind int0 G0) as Ha.
    unfold list_rule2_to_prop in *.
    unfold rule4_to_prop in *.
    simpl_Forall.
    tauto.
Qed.

Lemma solve_in_loop1_pre_spec H H' H_ind G h:
match solve_in_loop1_pre H H' H_ind G h with
| None => True
| Some _ =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  rule4_to_prop tm C H_ind ->
  rule4_to_prop tm C G
end.
Proof.
  gen H_ind h.
  induction G as [|G0 G]; intros.
  - cbn.
    unfold rule4_to_prop in *.
    simpl_Forall.
    tauto.
  - cbn.
    destruct G0 as [G0 [|]]; trivial.
    unfold if_Some.
    destruct_spec (solve_in_loop1_pre_0_spec); trivial.
    destruct p as [H_ind' h'].
    specialize (IHG H_ind' h').
    destruct_spec solve_in_loop1_pre; trivial.
    unfold rule4_push0 in *.
    unfold rule4_to_prop in *.
    unfold pair_list_rule2_to_prop in *.
    unfold list_rule2_to_prop in *.
    simpl_Forall.
    tauto.
Qed.

Lemma get_rule2'_spec H H' H_ind p' z dx dy:
match get_rule2' H H' H_ind p' z dx dy with
| None => True
| Some w =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  forall i0 i1,
  rule4_to_pred H_ind i0 i1 ->
  rule2_to_pred tm C w i0 i1
end.
Proof with trivial.
  unfold get_rule2',if_Some.
  destruct p' as [[p'|p']|p']...
  destruct p' as [[[pa [pb]] pc] [pd]].
  destruct z as [[z|z]|z].
  - destruct z as [[a [b]] [c]].
    destruct dx as [[dx|dx]|dx]...
    destruct dx as [[a0 _] _].
    destruct dy as [[dy|dy]|dy]...
    destruct dy as [[a1 _] _].
    destruct_spec get_rule2_from_spec...
    destruct (eqb (a0,a1) (int0,int1)).
    + destruct_spec rule2_lt_to_eq'_spec...
      intros.
      apply rule2_subst_spec'.
      intuition.
    + destruct (eqb (a0,a1) (int1,neg1))...
      destruct_spec rule2_lt_to_eq'_spec...
      intros.
      apply rule2_subst_spec'.
      intuition.
  - destruct z as [[[a [b]] c] [d]].
    destruct dx as [[dx|dx]|dx]...
    destruct dx as [[[a0 _] c0] _].
    destruct dy as [[dy|dy]|dy]...
    destruct dy as [[[a1 _] c1] _].
    destruct (eqb a pa).
    + destruct (eqb b pb).
      * destruct (eqb (a0,c0,(a1,c1)) (int1,int0,(int0,int1)))...
        destruct_spec get_rule2_from_spec'...
      * destruct (b<?pb)...
        destruct_spec get_rule2_from_spec...
        destruct (eqb (a0,c0,(a1,c1)) (int1,int0,(int0,int1)))...
        -- destruct_spec get_loop_cnt...
           intros.
           rewrite rule2_subst_spec.
           intuition.
        -- destruct (eqb (a0,c0,(a1,c1)) (int1,int1,(int0,neg1)))...
           destruct_spec get_loop_cnt...
           intros.
           rewrite rule2_subst_spec.
           intuition.
    + destruct (a<?pa)...
      destruct_spec get_rule2_from_spec...
      destruct (eqb (a0,c0,(a1,c1)) (int1,int0,(int0,int1)))...
      * destruct_spec get_loop_cnt...
        destruct_spec rule2_lt_to_eq_spec...
        intros.
        rewrite rule2_subst_spec.
        intuition.
      * destruct (eqb (a0,c0,(a1,c1)) (int1,int1,(int0,neg1)))...
        destruct_spec get_loop_cnt...
        destruct_spec rule2_lt_to_eq_spec...
        intros.
        rewrite rule2_subst_spec.
        intuition.
  - destruct z as [z].
    destruct_spec get_rule2_from_rule0_spec...
Qed.

Lemma solve_in_loop1_at_spec H H' H_ind h w:
match solve_in_loop1_at H H' H_ind h w with
| None => True
| Some _ =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  forall i0 i1,
  rule4_to_pred H_ind i0 i1 ->
  rule2_to_pred tm C w i0 i1
end.
Proof.
  unfold solve_in_loop1_at.
  unfold if_Some.
  refine (let '(p,(l1,r1,l2,r2),(z0,z1),(z00,z10),(z01,z11)):=h in _).
  destruct_spec (get_rule2'_spec); trivial.
  destruct_spec (get_rule2'_spec); trivial.
  destruct_spec (verify_rule2_spec); trivial.
  intros; apply H2; try tauto.
  - unfold rule2_to_prop. 
    intros.
    apply rule2_subst2_spec.
    apply H0; try tauto.
  - unfold rule2_to_prop. 
    intros.
    apply rule2_subst1_spec.
    apply H1; try tauto.
Qed.

Lemma rule4_add_spec' x i y i0 i1:
  rule4_to_pred x i0 i1 ->
  rule2_to_pred tm C y i0 i1 ->
  rule4_to_pred (rule4_add x i y) i0 i1.
Proof.
  gen i.
  induction x as [|[x0 x1] x]; intros.
  - cbn; trivial.
  - cbn - [eqb].
    unfold rule4_to_prop in *.
    destruct (eqb i int0);
      unfold rule4_to_pred in *;
      simpl_Forall.
    + unfold pair_list_rule2_to_pred in *.
      unfold list_rule2_to_pred in *.
      simpl_Forall.
      tauto.
    + intuition.
Qed.

Lemma solve_in_loop1_spec H H' H_ind G h:
match solve_in_loop1 H H' H_ind G h with
| None => True
| Some _ =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  forall i0 i1,
  rule4_to_pred H_ind i0 i1 ->
  list_rule2_to_pred G i0 i1
end.
Proof.
  gen H_ind h.
  induction G as [|G0 G]; intros.
  - cbn.
    unfold list_rule2_to_pred.
    intros.
    simpl_Forall.
    trivial.
  - cbn.
    destruct h as [|h0 h]; trivial.
    unfold if_Some.
    destruct_spec solve_in_loop1_at_spec; trivial.
    intros.
    specialize (IHG (rule4_add H_ind int0 G0) h).
    destruct_spec solve_in_loop1; trivial.
    intros.
    unfold list_rule2_to_pred in *.
    simpl_Forall.
    pose proof (rule4_add_spec' H_ind int0 G0 i0 i1) as Ha.
    intuition.
Qed.

Lemma list_rule3_to_rule4_spec x i0 i1:
  Forall (fun a => rule3_to_pred tm C a i0 i1) x <->
  rule4_to_pred (list_rule3_to_rule4 x) i0 i1.
Proof.
  induction x.
  - cbn.
    unfold rule4_to_pred.
    simpl_Forall.
    tauto.
  - cbn.
    unfold rule4_to_pred.
    simpl_Forall.
    rewrite <-IHx.
    rewrite rule3_to_list_rule2_spec.
    unfold pair_list_rule2_to_pred.
    unfold list_rule2_to_pred.
    repeat rewrite Forall_forall.
    cbn[In].
    intuition.
Qed.

Lemma rule4_upd_spec x i y i0 i1:
  list_rule2_to_pred y i0 i1 ->
  rule4_to_pred x i0 i1 ->
  rule4_to_pred (rule4_upd x i y) i0 i1.
Proof.
  gen i.
  induction x as [|[x0 x1] x]; intros.
  - unfold rule4_to_pred.
    simpl_Forall.
    trivial.
  - unfold rule4_to_pred.
    simpl_Forall.
    cbn - [eqb].
    unfold rule4_to_pred in *.
    unfold pair_list_rule2_to_pred in *.
    destruct (eqb i int0); simpl_Forall; intuition.
Qed.

Lemma list_rule2_to_prop_pred x:
  list_rule2_to_prop tm C x <->
  forall i0 i1, list_rule2_to_pred x i0 i1.
Proof.
  unfold list_rule2_to_prop.
  unfold list_rule2_to_pred.
  unfold rule2_to_prop.
  induction x.
  1: split; intros; simpl_Forall; tauto.
  split; intros; simpl_Forall.
  - intuition.
  - split; intros.
    + specialize (H i0 i1).
      simpl_Forall.
      tauto.
    + rewrite IHx.
      intros.
      specialize (H i0 i1).
      simpl_Forall.
      tauto.
Qed.

Lemma pair_list_rule2_to_prop_pred x:
  pair_list_rule2_to_prop tm C x <->
  forall i0 i1, pair_list_rule2_to_pred x i0 i1.
Proof.
  unfold pair_list_rule2_to_prop.
  unfold pair_list_rule2_to_pred.
  destruct x as [x0 x1].
  repeat rewrite list_rule2_to_prop_pred.
  split; intros.
  - intuition.
  - split; intros; specialize (H i0 i1); tauto.
Qed.


Lemma rule4_to_prop_pred x:
  rule4_to_prop tm C x <->
  forall i0 i1, rule4_to_pred x i0 i1.
Proof.
  unfold rule4_to_prop.
  unfold rule4_to_pred.
  induction x.
  1: split; intros; simpl_Forall; tauto.
  simpl_Forall.
  rewrite IHx.
  rewrite pair_list_rule2_to_prop_pred.
  split; intros; simpl_Forall.
  - intuition.
  - split; intros;
    specialize (H i0 i1); simpl_Forall; tauto.
Qed.

Lemma solve_rule4_0_spec H H' G h a:
match solve_rule4_0 H H' G h a with
| None => True
| Some _ =>
  rule4_to_prop tm C H ->
  rule4_to_prop tm C H' ->
  rule4_to_prop tm C G
end.
Proof with trivial.
  gen H' h a.
  induction G as [|[G0 G1] G]; intros.
  - cbn.
    unfold rule4_to_prop.
    simpl_Forall.
    trivial.
  - cbn - [eqb].
    destruct h as [|[[[[h1 h2] h3] k0] k1] h]...
    unfold if_Some.
    destruct_spec solve_pre_loop1_spec...
    destruct p as [H'0 h1'].
    destruct (eqb_spec G1 []) as [e|_].
    1:{
      specialize (IHG H'0 h (a+int1)).
      destruct_spec solve_rule4_0...
      intros.
      subst.
      unfold rule4_to_prop in *.
      unfold pair_list_rule2_to_prop in *.
      unfold list_rule2_to_prop in *.
      simpl_Forall.
      tauto.
    }
    pose proof (list_rule2_ind_spec' tm C G1 (to_N k0-1) (to_N k1)) as X1.
    destruct_spec (list_rule2_ind_spec tm C)...
    destruct p as [[[IG0 [IH IG]] IG1] IX1].
    destruct_spec solve_in_loop1_pre_spec...
    destruct_spec solve_in_loop1_pre_spec...
    destruct_spec solve_in_loop1_spec...
    specialize (IHG (rule4_upd H'0 a G1) h (a+int1)).
    destruct_spec solve_rule4_0...
    intros.
    specialize (H0 H6 H7).
    destruct H0 as [H0 H0a].
    specialize (H4 H6 H0).
    specialize (H3 H6).
    specialize (H2 H6 H0).
    assert (HT:rule4_to_prop tm C [] <-> True). {
      unfold rule4_to_prop.
      simpl_Forall.
      tauto.
    }
    rewrite HT in *.
    specialize (H2 I).
    specialize (H1 H2).
    specialize (X1 H2).
    match type of X1 with
    | ?a->_ => assert (X2:a)
    end. {
      intros.
      specialize (H4 i0 i1).
      rewrite rule3_to_list_rule2_spec.
      apply H4.
      unfold rule4_push0.
      gen H8.
      rewrite list_rule3_to_rule4_spec.
      unfold list_rule3_to_rule4.
      unfold rule4_to_pred.
      unfold pair_list_rule2_to_pred.
      unfold list_rule2_to_pred.
      simpl_Forall.
      repeat rewrite Forall_map.
      pose proof (Forall_rev).
      intuition.
    }
    specialize (X1 X2).
    pose proof (rule4_upd_spec H'0 a IX1) as Hu.
    match type of H3 with
    | ?a->_ => assert (X3:a)
    end. {
      rewrite rule4_to_prop_pred.
      intros.
      apply Hu.
      - gen i0 i1.
        rewrite <-list_rule2_to_prop_pred.
        tauto.
      - gen i0 i1.
        rewrite <-rule4_to_prop_pred.
        tauto.
    }
    specialize (H3 X3 I).
    assert (X4:list_rule2_to_prop tm C G1). {
      apply H1; try tauto.
      unfold rule4_to_prop in *.
      epose proof (Forall_rev H3) as X.
      rewrite rev_involutive in X.
      apply X.
    }
    specialize (IHG H6).
    rewrite rule4_to_prop_pred in IHG.
    eassert (X5:_). {
      apply IHG.
      intros.
      apply rule4_upd_spec.
      - gen i0 i1.
        rewrite <-list_rule2_to_prop_pred.
        tauto.
      - gen i0 i1.
        rewrite <-rule4_to_prop_pred.
        tauto.
    }
    unfold rule4_to_prop.
    unfold pair_list_rule2_to_prop.
    simpl_Forall.
    tauto.
Qed.
End C_ctx.

Lemma rule4_new_spec C n:
  rule4_to_prop tm C (rule4_new n).
Proof.
  unfold rule4_new,rule4_to_prop,pair_list_rule2_to_prop.
  rewrite Forall_forall; intros.
  destruct x.
  pose proof (repeat_spec _ _ _ H).
  inverts H0.
  unfold list_rule2_to_prop.
  simpl_Forall.
  tauto.
Qed.

Lemma solve_rule4_spec G h:
match solve_rule4 G h with
| None => True
| Some _ =>
  forall C,
  rule4_to_prop tm C G
end.
Proof.
  unfold solve_rule4,if_Some.
  destruct_spec solve_rule4_O_spec; trivial.
  destruct (rule4_lt_r_S G (subst_rule4_Sc G)) eqn:E1; trivial.
  destruct (solve_rule4_0 G (rule4_new (Datatypes.length l)) l h int0) eqn:E2; trivial.
  eapply N.peano_ind.
  1: apply H.
  intro C.
  pose proof (rule4_lt_r_S_spec tm C G (subst_rule4_Sc G)) as H0.
  rewrite E1 in H0.
  pose proof (solve_rule4_0_spec C G (rule4_new (Datatypes.length l)) l h int0) as H1.
  rewrite E2 in H1.
  rewrite (subst_rule4_Sc_spec tm C G) in H0.
  intros H2.
  applys_eq H0; try tauto; try lia.
  intros.
  apply H1; try tauto.
  apply rule4_new_spec.
Qed.
End RelId_ctx.
End check_loop_ctx.

Definition init_State S T :=
Build_State
(Seg1xIdAlloc.id_alloc_make S)
(Rule0IdAlloc.id_alloc_make S)
(Mem.hmap_make S)
(make S None)
T.

Definition get_rule0_id(x:Rule0.T)(st:State):option (int*State) :=
let (sid,rid,mem,rinfo,T_):=st in
Rule0IdAlloc.get_or_alloc_id x rid &&& (fun '(id,rid) =>
Some (id,Build_State sid rid mem rinfo T_)).

Inductive State' :=
| CheckStep1(w0 w1:Rule0.T)
| CheckRec(w0 w1:Rule0.T)
| Ret(w0:Config0.T)(w1:Rule0.T)
| Call(w0:Config0.T)
.

Section run_ctx.
Hypothesis tm:TM.
Hypothesis max_bsz:nat.

Definition add_rule(x1 x2:Rule0.T)(st:State):option (Rule0.T*State) :=
Rule0.follow_rule x1 x2 &&& (fun '(x3,info) =>
get_rule0_id x1 st &&& (fun '(id1,st) =>
get_rule0_id x2 st &&& (fun '(id2,st) =>
get_rule0_id x3 st &&& (fun '(id3,st) =>
let (sid,rid,mem,rinfo,T_):=st in
let rinfo := (if (PrimInt63.ltb id1 id3 && PrimInt63.ltb id2 id3 && is_None rinfo.[id3])%bool then
  rinfo.[id3<-Some (x3,info,(id1,id2))]
else rinfo) in
Some (x3,Build_State sid rid mem rinfo T_)
)))).

Definition upd_mem(w0:Config0.T)(w1:Rule0.T)(st:State):State :=
let (sid,rid,mem,rinfo,T_):=st in
let mem := Mem.hmap_set w0 w1 mem in
Build_State sid rid mem rinfo (T_).

Fixpoint run(st':State')(st:State)(n:nat)(is_top:bool):option ((option Rule0.T)*State) :=
match n with
| O => Some (None,init_State (Uint63.of_Z 0) (Uint63.of_Z 0))
| S n =>
  if PrimInt63.lesb st.(rest_T) (snd st.(rule0_id)) then Some (None,st) else
  match st' with
  | CheckStep1 w0 w1 =>
    let '(l02,r02,s02,sgn02) := snd w0 in
    (if (eqb r02 [] && negb is_top)%bool then
      run (Ret (fst w0) w1) st n is_top
    else
      let m02 := hd s0 r02 in
      if is_None (tm (s02,m02)) then
      run (Ret (fst w0) w1) st n is_top
      else
      Rule0.step1_rule s02 m02 sgn02 tm &&& (fun dw =>
      Rule0.follow_rule w0 dw &&& (fun '(w0,_) =>
      add_rule w1 dw st &&& (fun '(w1,st) =>
      let '(l02,r02,s02,sgn02) := snd w0 in
      run (if eqb r02 nil then CheckStep1 w0 w1 else CheckRec w0 w1) st n is_top
      ))))
  | CheckRec w0 w1 =>
    run (Call (snd w1)) st n false &&& (fun '(dw,st) =>
    match dw with
    | None => Some (None,st)
    | Some dw =>
    Rule0.follow_rule w0 dw &&& (fun '(w0,_) =>
    add_rule w1 dw st &&& (fun '(w1,st) =>
    run (CheckStep1 w0 w1) st n is_top
    ))
    end)
  | Call w0 =>
    match if is_top then None else Mem.hmap_get w0 st.(mem) with
    | Some v =>
      if Rule0IdAlloc.get_id v st.(rule0_id) then Some (Some v,st) else None
    | None =>
      let '(l0,r0,s0,sgn0) := w0 in
      run (CheckStep1 (Rule0.step0_rule w0) (Rule0.step0_rule ([],[],s0,sgn0))) st n is_top
    end
  | Ret w0 w1 =>
    let st := upd_mem w0 w1 st in
    Some (Some w1,st)
  end
end.

Definition run0 maxS maxT :=
  run (Call ([],[],q0,R)) (init_State maxS maxT) MAXT true.

Inductive State'_WF: State'->Prop :=
| CheckStep1_WF w0 w1
  (H_w1:Rule0.to_prop w1 tm):
  State'_WF (CheckStep1 w0 w1)
| CheckRec_WF w0 w1
  (H_w1:Rule0.to_prop w1 tm):
  State'_WF (CheckRec w0 w1)
| Ret_WF w0 w1
  (H_w1:Rule0.to_prop w1 tm):
  State'_WF (Ret w0 w1)
| Call_WF w0: State'_WF (Call w0)
.

Inductive State_WF: State->Prop :=
| State_WF_intro sid rid mem info rest_T
  (H_rid_WF:Rule0IdAlloc.id_alloc_WF rid)
  (H_rid:forall x,
  match Rule0IdAlloc.get_id x rid with
  | Some _ => Rule0.to_prop x tm
  | _ => True
  end):
  State_WF (Build_State sid rid mem info rest_T)
.

Lemma init_State_spec a b:
  State_WF (init_State a b).
Proof.
  unfold init_State.
  econstructor.
  - eapply Rule0IdAlloc.id_alloc_make_WF.
  - intros x.
    unfold Rule0IdAlloc.get_id.
    unfold Rule0IdAlloc.id_alloc_make.
    rewrite Rule0IdAlloc.MapToId.hmap_get_make; trivial.
Qed.

Lemma get_rule0_id_spec w0 st:
match get_rule0_id w0 st with
| Some (_,st0) =>
  Rule0.to_prop w0 tm ->
  State_WF st ->
  State_WF st0
| None => True
end.
Proof.
  unfold get_rule0_id,if_Some.
  destruct st.
  pose proof (Rule0IdAlloc.get_or_alloc_id_WF w0 rule0_id0).
  destruct_spec Rule0IdAlloc.get_or_alloc_id; trivial.
  destruct p as [id rid].
  intros Hw0 H0.
  inverts H0.
  constructor.
  - tauto.
  - intros.
    specialize (H_rid x).
    specialize (H H_rid_WF).
    destruct H as [H [Ha Hb]].
    destruct (eqb_spec x w0).
    + subst.
      rewrite H. tauto.
    + specialize (Hb _ n).
      rewrite Hb. tauto.
Qed.

Lemma add_rule_spec w0 w1 st:
match add_rule w0 w1 st with
| Some (w2,st0) =>
  Rule0.to_prop w0 tm ->
  Rule0.to_prop w1 tm ->
  State_WF st ->
  (State_WF st0 /\
  Rule0.to_prop w2 tm)
| None => True
end.
Proof.
  unfold add_rule,if_Some.
  destruct_spec Rule0.follow_rule_spec; trivial.
  specialize (H tm).
  destruct p as [x3 info].
  destruct_spec get_rule0_id_spec; trivial.
  destruct p as [id1 st1].
  destruct_spec get_rule0_id_spec; trivial.
  destruct p as [id2 st2].
  destruct_spec get_rule0_id_spec; trivial.
  destruct p as [id3 st3].
  destruct st3 as [sid rid mem0 rinfo T_].
  intros.
  split.
  2: tauto.
  eassert (X0:_) by (apply H2; tauto).
  inverts X0.
  constructor; tauto.
Qed.

Lemma run_spec st' st n is_top:
State'_WF st' ->
State_WF st ->
match run st' st n is_top with
| None => True
| Some (Some w,st'') =>
  State_WF st'' /\
  Rule0.to_prop w tm
| Some (None,st'') =>
  State_WF st''
end.
Proof with trivial.
  gen st' st is_top.
  induction n; intros.
  - cbn.
    intros.
    apply init_State_spec.
  - cbn[run].
    unfold if_Some.
    destruct_spec PrimInt63.lesb...
    destruct st'.
    + destruct w0 as [w00 w01].
      unfold fst,snd.
      destruct w01 as [[[l02 r02] s02] sgn02].
      inverts H.
      destruct (eqb r02 [] && negb is_top)%bool.
      * apply IHn; try tauto.
        constructor; tauto.
      * destruct (is_None (tm (s02, hd s0 r02))).
        -- apply IHn; try tauto.
           constructor; tauto.
        -- destruct_spec Rule0.step1_rule_spec...
           destruct_spec Rule0.follow_rule_spec...
           specialize (H2 tm).
           destruct p as [w0 _].
           destruct_spec add_rule_spec; trivial.
           destruct p as [w2 st0].
           destruct w0 as [w00' w01'].
           destruct w01' as [[[l03 r03] s03] sgn03].
           destruct (eqb r03 []).
           ++ apply IHn.
              ** constructor; tauto.
              ** tauto.
           ++ apply IHn.
              ** constructor; tauto.
              ** tauto.
    + pose proof (IHn (Call (snd w1)) st false) as IHn'.
      destruct_spec run...
      destruct p as [[dw|] st0].
      * unshelve epose proof (IHn' _ _) as [Hst0 Hdw].
        1: constructor.
        1: tauto.
        destruct_spec Rule0.follow_rule_spec...
        destruct p as [w2 _].
        destruct_spec add_rule_spec...
        destruct p as [w3 st1].
        specialize (H2 tm).
        inverts H.
        apply IHn.
        -- constructor; tauto.
        -- tauto.
      * unshelve epose proof (IHn' _ _) as Hst0.
        1: constructor.
        1: tauto.
        tauto.
    + inverts H.
      split. 2: tauto.
      unfold upd_mem.
      inverts H0.
      constructor; tauto.
    + destruct (if is_top then None else Mem.hmap_get w0 (mem st)).
      * destruct (Rule0IdAlloc.get_id v (rule0_id st)) eqn:E...
        split.
        -- tauto.
        -- inverts H0.
           cbn in E.
           specialize (H_rid v).
           rewrite E in H_rid.
           apply H_rid.
      * destruct w0 as [[[l0 r0] s2] sgn0].
        apply IHn.
        -- constructor.
           apply Rule0.step0_rule_spec.
        -- tauto.
Qed.

Lemma run0_spec maxS maxT:
match run0 maxS maxT with
| None => True
| Some (_,st) =>
  State_WF st
end.
Proof.
  unfold run0.
  destruct_spec run_spec; trivial.
  destruct p as [p st].
  destruct p as [w|].
  - apply H.
    + constructor.
    + apply init_State_spec.
  - apply H.
    + constructor.
    + apply init_State_spec.
Qed.

Definition decide_loop2_dbg(min_b:int*int)(n_merge n_skip:nat)(loop1_as_loop2:bool)(maxk maxT:int) :=
run0 maxT maxT &&& (fun '(_,st) =>
let ctx1:=(find_all_loop1 st min_b) in
let ctx1':=map (fun '(p,a,d,b) => (to_N a,to_N d,to_N b)) ctx1 in
(find_loop2 n_merge n_skip loop1_as_loop2 ctx1) &&& (fun ctx =>
int_range_omap (fun k =>
Some (
match check_loop2' st ctx k with
| Some v => (inl k)
| None => (inr (k))
end)
) maxk &&& (fun v => Some (v,ctx1'))
) |||
Some ([],ctx1')
).

Definition decide_loop2_dbg2(min_b:int*int)(n_merge n_skip:nat)(loop1_as_loop2:bool)(k maxT:int) :=
run0 maxT maxT &&& (fun '(_,st) =>
let ctx1:=(find_all_loop1 st min_b) in
let ctx1':=map (fun '(p,a,d,b) => (to_N a,to_N d,to_N b)) ctx1 in
(find_loop2 n_merge n_skip loop1_as_loop2 ctx1) &&& (fun ctx =>
check_loop2'dbg st ctx k
)
).
Definition decide_loop2_dbg_ctx(min_b:int*int)(n_merge n_skip:nat)(loop1_as_loop2:bool)(maxT:int) :=
run0 maxT maxT &&& (fun '(_,st) =>
let ctx1:=(find_all_loop1 st min_b) in
let ctx1':=map (fun '(p,a,d,b) => (to_N a,to_N d,to_N b)) ctx1 in
(find_loop2 n_merge n_skip loop1_as_loop2 ctx1)
).

Definition get_graph(maxT:int) :=
run0 maxT maxT &&& (fun '(_,st) =>
let ls := st.(rule0_info) in
int_range_omap (fun i =>
Some (
match ls.[i] with
| None => []
| Some (_,_,(z0,z1)) =>
  (to_N i,to_N z0)::(to_N i,to_N z1)::nil
end)
) (maxT)
) &&& (fun ls => Some (concat ls)).

Definition decide_loop2(min_b:int*int)(n_merge n_skip:nat)(loop1_as_loop2:bool)(k maxT:int):bool :=
o2b (
run0 maxT maxT &&& (fun '(_,st) =>
(find_loop2 n_merge n_skip loop1_as_loop2 (find_all_loop1 st min_b)) &&& (fun ctx =>
check_loop2' st ctx k &&& (fun ls =>
let (loop2,loop2r):=split ls in
solve_rule4 st ctx k loop2 loop2r &&& (fun _ =>
if rule4_check_sigma_score loop2 then Some tt else None
))))).

Lemma decide_loop2_spec min_b n_merge n_skip loop1_as_loop2 k maxT:
match decide_loop2 min_b n_merge n_skip loop1_as_loop2 k maxT with
| true =>
  ~halts tm c0
| _ => True
end.
Proof with trivial.
  unfold decide_loop2,if_Some,o2b.
  destruct_spec run0_spec...
  destruct p as [_ st].
  destruct_spec find_loop2...
  destruct_spec check_loop2'...
  destruct (split l0).
  pose proof ((fun l1 l2 a => solve_rule4_spec st l k tm a l1 l2) l1 l2) as Hr4.
  destruct_spec solve_rule4...
  destruct_spec (rule4_check_sigma_score_spec tm)...
  apply H1,Hr4.
  inverts H.
  assumption.
Qed.

Definition nat2int(x:nat):int := Uint63.of_Z (Z.of_nat x).

Lemma decide_loop2_spec' min_b n_skip k maxT:
  decide_loop2 (nat2int (fst min_b),nat2int (snd min_b)) 1%nat n_skip false (Uint63.of_Z (Z.of_nat k)) (Uint63.of_Z (Z.of_N maxT)) = true ->
  ~halts tm c0.
Proof.
  epose proof (decide_loop2_spec _ _ _ _ _ _) as H.
  intros H0.
  rewrite H0 in H.
  tauto.
Qed.

Lemma decide_loop1_spec' min_b n_skip k maxT:
  decide_loop2 (nat2int (fst min_b),nat2int (snd min_b)) 1%nat n_skip true (Uint63.of_Z (Z.of_nat k)) (Uint63.of_Z (Z.of_N maxT)) = true ->
  ~halts tm c0.
Proof.
  epose proof (decide_loop2_spec _ _ _ _ _ _) as H.
  intros H0.
  rewrite H0 in H.
  tauto.
Qed.

End run_ctx.

End RRBA.


