From BusyCoq Require Import Individual.
Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import FSets.FMapPositive.

Notation "x || y" := (if x then true else y) : bool_scope.
Notation "x && y" := (if x then y else false) : bool_scope.
Open Scope bool.

Lemma or_false_iff (a b:bool):
  (a || b) = false <->
  a = false /\ b = false.
Proof.
  destruct a,b; tauto.
Qed.

Lemma and_true_iff (a b:bool):
  (a && b) = true <->
  a = true /\ b = true.
Proof.
  destruct a,b; tauto.
Qed.




Ltac destruct_spec_expr e f :=
match e with
| match ?a with _ => _ end => destruct_spec_expr a f
| if ?a then _ else _ => destruct_spec_expr a f
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





Fixpoint exgcdn(n:nat)(a b:Z):Z*Z :=
(match n with
| O => (1,0)
| S n0 =>
  match b with
  | Z0 => (1,0)
  | _ =>
    let (y,x):=exgcdn n0 b (a mod b) in
    (x,y-a/b*x)
  end
end)%Z.

Definition N_to_Pos(x:N):=
match x with
| N0 => xH
| Npos x0 => x0
end.

Definition exgcd(a b:N):N*N :=
  let (x,y):=
  exgcdn ((Nat.max (Pos.size_nat (N_to_Pos a)) (Pos.size_nat (N_to_Pos b)))*2) (Z.of_N a) (Z.of_N b) in
  (Z.to_N (if x <? 0 then (x+Z.of_N b) else x),Z.to_N (if y <? 0 then (y+Z.of_N a) else y))%Z.





Module Inductive(Ctx:Ctx).

Module TM := TM Ctx. Export TM.

Definition multistep' tm (p:bool) s0 s1 :=
if p then s0-[tm]->+s1 else s0-[tm]->*s1.


Definition id_t := positive.

Inductive type_t :=
| nat_t
| seg_t
| side_t
.

Definition to_type(x:type_t):Type :=
match x with
| nat_t => N
| seg_t => list Sym
| side_t => side
end.


Inductive nat_expr :=
| from_nat(n:N)
| nat_add(a b:nat_expr)
| nat_mul(a b:nat_expr)
| nat_var(i:id_t)
| nat_ivar
.

Inductive seg_expr :=
| seg_sym(a:Sym)
| seg_concat(a:seg_expr)(b:seg_expr)
| seg_repeat(a:seg_expr)(n:nat_expr)
| seg_var(i:id_t)
.

Inductive side_expr :=
| side_0inf
| side_var(i:id_t)
| side_concat(a:seg_expr)(b:side_expr)
.

Definition to_expr_type(x:type_t):Type :=
match x with
| nat_t => nat_expr
| seg_t => seg_expr
| side_t => side_expr
end.

Definition expr_expr := {x:type_t & to_expr_type x}.
Definition make_expr_expr(t:type_t)(x:to_expr_type t):expr_expr.
  exists t.
  apply x.
Defined.


Definition config_expr:Type := side_expr*side_expr*Q*dir.

Inductive prop0_expr :=
| nat_eq(a b:nat_expr)
| seg_eq(a b:seg_expr)
| side_eq(a b:side_expr)
| config_eq(a b:config_expr)
| false_prop0
| multistep_expr(a b:config_expr)(n:nat_expr)
| multistep'_expr(a b:config_expr)(n:bool)
.

Definition prop_expr:Type :=
  (list prop0_expr)*(list prop0_expr).



Fixpoint nat_expr_eqb(a b:nat_expr):bool :=
match a,b with
| from_nat a0,from_nat b0 => (a0 =? b0)%N
| nat_add a0 a1,nat_add b0 b1 => (nat_expr_eqb a0 b0) && (nat_expr_eqb a1 b1)
| nat_mul a0 a1,nat_mul b0 b1 => (nat_expr_eqb a0 b0) && (nat_expr_eqb a1 b1)
| nat_var a0,nat_var b0 => (a0 =? b0)%positive
| nat_ivar,nat_ivar => true
| _,_ => false
end.

Ltac solve_Bool_reflect :=
  try (constructor; congruence).

Lemma nat_expr_eqb_spec(a b:nat_expr): Bool.reflect (a=b) (nat_expr_eqb a b).
Proof.
  gen b.
  induction a; intros b; destruct b; cbn.
  all: solve_Bool_reflect.
  - destruct (N.eqb_spec n n0);
    solve_Bool_reflect.
  - destruct (IHa1 b1),(IHa2 b2); subst; cbn;
    solve_Bool_reflect.
  - destruct (IHa1 b1),(IHa2 b2); subst; cbn;
    solve_Bool_reflect.
  - destruct (Pos.eqb_spec i i0);
    solve_Bool_reflect.
Qed.

Fixpoint seg_expr_eqb(a b:seg_expr):bool :=
match a,b with
| seg_sym a0,seg_sym b0 => sym_eqb a0 b0
| seg_concat a0 a1,seg_concat b0 b1 => seg_expr_eqb a0 b0 && seg_expr_eqb a1 b1
| seg_repeat a0 an,seg_repeat b0 bn => seg_expr_eqb a0 b0 && nat_expr_eqb an bn
| seg_var a0,seg_var b0 => (a0 =? b0)%positive
| _,_ => false
end.

Lemma seg_expr_eqb_spec(a b:seg_expr): Bool.reflect (a=b) (seg_expr_eqb a b).
Proof.
  gen b.
  induction a; intros b; destruct b; cbn.
  all: solve_Bool_reflect.
  - destruct (sym_eqb_spec a a0);
    solve_Bool_reflect.
  - destruct (IHa1 b1),(IHa2 b2); subst; cbn;
    solve_Bool_reflect.
  - destruct (IHa b),(nat_expr_eqb_spec n n0); subst; cbn;
    solve_Bool_reflect.
  - destruct (Pos.eqb_spec i i0);
    solve_Bool_reflect.
Qed.

Fixpoint side_expr_eqb(a b:side_expr):bool :=
match a,b with
| side_0inf,side_0inf => true
| side_var a0,side_var b0 => (a0 =? b0)%positive
| side_concat a0 a1,side_concat b0 b1 => seg_expr_eqb a0 b0 && side_expr_eqb a1 b1
| _,_ => false
end.

Lemma side_expr_eqb_spec(a b:side_expr): Bool.reflect (a=b) (side_expr_eqb a b).
Proof.
  gen b.
  induction a; intros b; destruct b; cbn.
  all: solve_Bool_reflect.
  - destruct (Pos.eqb_spec i i0);
    solve_Bool_reflect.
  - destruct (IHa b),(seg_expr_eqb_spec a a1); subst; cbn;
    solve_Bool_reflect.
Qed.

Definition dir_eqb(a b:dir):bool :=
match a,b with
| L,L | R,R => true
| _,_ => false
end.

Lemma dir_eqb_spec(a b:dir): Bool.reflect (a=b) (dir_eqb a b).
Proof.
  destruct a,b;
  solve_Bool_reflect.
Qed.

Definition config_expr_eqb(a b:config_expr):bool :=
let '(l1,r1,s1,sgn1) := a in
let '(l2,r2,s2,sgn2) := b in
(q_eqb s1 s2) && (dir_eqb sgn1 sgn2) &&
(side_expr_eqb l1 l2) && (side_expr_eqb r1 r2).

Lemma config_expr_eqb_spec(a b:config_expr): Bool.reflect (a=b) (config_expr_eqb a b).
Proof.
  destruct a as [[[l1 r1] s1] sgn1].
  destruct b as [[[l2 r2] s2] sgn2].
  cbn.
  destruct (q_eqb_spec s1 s2); solve_Bool_reflect.
  destruct (dir_eqb_spec sgn1 sgn2); solve_Bool_reflect.
  destruct (side_expr_eqb_spec l1 l2); solve_Bool_reflect.
  destruct (side_expr_eqb_spec r1 r2); solve_Bool_reflect.
Qed.

Definition prop0_eqb(a b:prop0_expr):bool :=
match a,b with
| nat_eq a0 a1,nat_eq b0 b1 => nat_expr_eqb a0 b0 && nat_expr_eqb a1 b1
| seg_eq a0 a1,seg_eq b0 b1 => seg_expr_eqb a0 b0 && seg_expr_eqb a1 b1
| side_eq a0 a1,side_eq b0 b1 => side_expr_eqb a0 b0 && side_expr_eqb a1 b1
| config_eq a0 a1,config_eq b0 b1 => config_expr_eqb a0 b0 && config_expr_eqb a1 b1
| false_prop0,false_prop0 => true
| multistep_expr a0 a1 an,multistep_expr b0 b1 bn =>
  config_expr_eqb a0 b0 && config_expr_eqb a1 b1 && nat_expr_eqb an bn
| multistep'_expr a0 a1 an,multistep'_expr b0 b1 bn =>
  config_expr_eqb a0 b0 && config_expr_eqb a1 b1 && Bool.eqb an bn
| _,_ => false
end.

Lemma prop0_eqb_spec a b: Bool.reflect (a=b) (prop0_eqb a b).
Proof.
  destruct a,b; cbn; solve_Bool_reflect.
  - destruct (nat_expr_eqb_spec a a0); solve_Bool_reflect.
    destruct (nat_expr_eqb_spec b0 b); solve_Bool_reflect.
  - destruct (seg_expr_eqb_spec a a0); solve_Bool_reflect.
    destruct (seg_expr_eqb_spec b0 b); solve_Bool_reflect.
  - destruct (side_expr_eqb_spec a a0); solve_Bool_reflect.
    destruct (side_expr_eqb_spec b0 b); solve_Bool_reflect.
  - destruct (config_expr_eqb_spec a a0); solve_Bool_reflect.
    destruct (config_expr_eqb_spec b0 b); solve_Bool_reflect.
  - destruct (config_expr_eqb_spec a a0); solve_Bool_reflect.
    destruct (config_expr_eqb_spec b0 b); solve_Bool_reflect.
    destruct (nat_expr_eqb_spec n n0); solve_Bool_reflect.
  - destruct (config_expr_eqb_spec a a0); solve_Bool_reflect.
    destruct (config_expr_eqb_spec b0 b); solve_Bool_reflect.
    destruct (Bool.eqb_spec n n0); solve_Bool_reflect.
Qed.

Fixpoint list_prop0_eqb(a b:list prop0_expr):bool :=
match a,b with
| nil,nil => true
| a0::a1,b0::b1 =>
  prop0_eqb a0 b0 &&
  list_prop0_eqb a1 b1
| _,_ => false
end.

Lemma list_prop0_eqb_spec a b: Bool.reflect (a=b) (list_prop0_eqb a b).
Proof.
  gen b.
  induction a; destruct b; cbn; solve_Bool_reflect.
  - specialize (IHa b).
    destruct (prop0_eqb_spec a p); solve_Bool_reflect.
    destruct IHa; solve_Bool_reflect.
Qed.

Definition prop_eqb(a b:prop_expr):bool :=
let (a0,a1):=a in
let (b0,b1):=b in
list_prop0_eqb a0 b0 &&
list_prop0_eqb a1 b1.

Lemma prop_eqb_spec a b: Bool.reflect (a=b) (prop_eqb a b).
Proof.
  destruct a as [a0 a1].
  destruct b as [b0 b1].
  cbn.
  destruct (list_prop0_eqb_spec a0 b0); solve_Bool_reflect.
  destruct (list_prop0_eqb_spec a1 b1); solve_Bool_reflect.
Qed.



Definition affine_map := list (nat_expr*Z).
Fixpoint affine_map_upd'(f:affine_map)(x:nat_expr)(u:Z):affine_map*bool :=
match f with
| nil => (nil,false)
| (x0,y0)::f1 =>
  if nat_expr_eqb x0 x then
    ((x0,(y0+u)%Z)::f1,true)
  else
    let '(f2,t):=affine_map_upd' f1 x u in
    ((x0,y0)::f2,t)
end.

Definition affine_map_upd(f:affine_map)(x:nat_expr)(u:Z):affine_map :=
let '(f1,t):=affine_map_upd' f x u in
if t then f1 else (x,u)::f1.


Fixpoint from_affine_map(f:affine_map):nat_expr*nat_expr :=
match f with
| nil => (from_nat 0,from_nat 0)
| (x0,y0)::f0 =>
  let (v1,v2):=from_affine_map f0 in
  match y0 with
  | Zpos y1 => (nat_add v1 (nat_mul x0 (from_nat (Npos y1))),v2)
  | Zneg y1 => (v1,nat_add v2 (nat_mul x0 (from_nat (Npos y1))))
  | Z0 => (v1,v2)
  end
end.

Fixpoint affine_map_gcd(f:affine_map):Z :=
match f with
| nil => Z0
| (x0,y0)::f1 =>
  let g := affine_map_gcd f1 in
  if nat_expr_eqb x0 (from_nat 1) then g else (Z.gcd g y0)
end.

Fixpoint affine_map_divide(f:affine_map)(g:Z):Prop :=
match f with
| nil => True
| (x0,y0)::f1 =>
  (if nat_expr_eqb x0 (from_nat 1) then True else (Z.divide g y0)) /\
  (affine_map_divide f1 g)
end.

Lemma affine_map_divide_trans f g0 g1:
  Z.divide g1 g0 ->
  affine_map_divide f g0 ->
  affine_map_divide f g1.
Proof.
  intros H.
  induction f as [|[x0 y0] f]; intros; cbn.
  1: trivial.
  cbn in H0.
  destruct (nat_expr_eqb_spec x0 (from_nat 1)).
  1: tauto.
  split. 2: tauto.
  eapply Z.divide_trans; eauto; tauto.
Qed.

Lemma affine_map_gcd_spec f:
  affine_map_divide f (affine_map_gcd f).
Proof.
  induction f as [|[x0 y0] f]; cbn.
  1: trivial.
  destruct (nat_expr_eqb_spec x0 (from_nat 1)).
  1: tauto.
  remember (affine_map_gcd f) as g.
  pose proof (Z.gcd_divide_l g y0) as H.
  pose proof (Z.gcd_divide_r g y0) as H0.
  split. 1: tauto.
  clear H0.
  eapply affine_map_divide_trans; eauto.
Qed.

Fixpoint affine_map_div(f:affine_map)(g:Z):(affine_map*Z) :=
match f with
| nil => (nil,Z0)
| (x0,y0)::f1 =>
  let (f2,m2) := affine_map_div f1 g in
  ((x0,y0/g)::f2,(if nat_expr_eqb x0 (from_nat 1) then (m2+(y0 mod g)) else m2))%Z
end.

Fixpoint add_to_affine_map(a:nat_expr)(sgn:Z)(f:affine_map):affine_map :=
match a with
| nat_add a0 a1 =>
  let f0 := add_to_affine_map a0 sgn f in
  add_to_affine_map a1 sgn f0
| nat_mul a0 (from_nat a1) =>
  add_to_affine_map a0 (sgn*(Z.of_N a1))%Z f
| from_nat a1 => affine_map_upd f (from_nat 1) (sgn*(Z.of_N a1))%Z
| _ => affine_map_upd f a sgn
end.




Definition simpl_nat_expr(x:nat_expr) :=
match x with
| nat_add (from_nat 0) b => b
| nat_add (from_nat a) b => nat_add b (from_nat a)
| nat_add (nat_add a (from_nat b)) c => nat_add (nat_add a c) (from_nat b)
| nat_mul (from_nat 1) b => b
| nat_mul b (from_nat 1) => b
| _ => x
end.

Fixpoint simpls_nat_expr(x:nat_expr) :=
match x with
| nat_add a b => simpl_nat_expr (nat_add (simpls_nat_expr a) (simpls_nat_expr b))
| nat_mul a b => simpl_nat_expr (nat_mul (simpls_nat_expr a) (simpls_nat_expr b))
| _ => x
end.

Definition simpl_nat_expr_by_affine_map(a:nat_expr) :=
let f := add_to_affine_map a 1 nil in
let (v1,v2) := from_affine_map f in
if nat_expr_eqb v2 (from_nat 0) then v1 else a.


Definition list_prop0_from_affine_map f :=
let (v1,v2) := from_affine_map f in
if nat_expr_eqb v1 v2 then [] else [nat_eq (simpls_nat_expr v1) (simpls_nat_expr v2)].

Definition from_affine_map_simpl_div(f:affine_map):list prop0_expr :=
let g := affine_map_gcd f in
if (1 <? g)%Z then
  let (f0,g0) := affine_map_div f g in
  if (g0 =? 0)%Z then list_prop0_from_affine_map f0
  else if (g0 mod g =? 0)%Z then list_prop0_from_affine_map f
  else [false_prop0]
else list_prop0_from_affine_map f.



Definition solve_nat_eq(a b:nat_expr):list prop0_expr :=
let f := add_to_affine_map a 1 nil in
let f0 := add_to_affine_map b (-1) f in
from_affine_map_simpl_div f0.

Fixpoint solve_seg_eq(a b:seg_expr):list prop0_expr :=
match a,b with
| seg_sym a0,seg_sym b0 => if sym_eqb a0 b0 then [] else [false_prop0]
| seg_concat a0 a1,seg_concat b0 b1 => (solve_seg_eq a0 b0) ++ (solve_seg_eq a1 b1)
| seg_repeat a0 a1,seg_repeat b0 b1 => (solve_seg_eq a0 b0) ++ (solve_nat_eq a1 b1)
| seg_var a0,seg_var b0 => if (a0=?b0)%positive then [] else [seg_eq a b]
| _,_ => [seg_eq a b]
end.

Fixpoint solve_side_eq(a b:side_expr):list prop0_expr :=
match a,b with
| side_0inf,side_0inf => []
| side_var a0,side_var b0 => if (a0=?b0)%positive then [] else [side_eq a b]
| side_concat a0 a1,side_concat b0 b1 => (solve_seg_eq a0 b0) ++ (solve_side_eq a1 b1)
| _,_ => [side_eq a b]
end.

Definition solve_config_eq(a b:config_expr):list prop0_expr :=
let '(l1,r1,s1,d1):=a in
let '(l2,r2,s2,d2):=b in
(if q_eqb s1 s2 && dir_eqb d1 d2 then (solve_side_eq l1 l2) ++ (solve_side_eq r1 r2) else [false_prop0]).

Definition solve_eq(x:prop0_expr):list prop0_expr :=
match x with
| nat_eq a b => solve_nat_eq a b
| seg_eq a b => solve_seg_eq a b
| side_eq a b => solve_side_eq a b
| config_eq a b => solve_config_eq a b
| _ => [x]
end.

Definition solve_eqs x :=
  flat_map solve_eq x.

Definition prop_solve_eq(x:prop_expr) :=
let (H,G):=x in (solve_eqs H,G).

Fixpoint has_false(x:list prop0_expr) :=
match x with
| nil => false
| false_prop0::t => true
| _::t => has_false t
end.

Definition prop_has_false(x:prop_expr) :=
let (H,G):=x in has_false H.




(*
  syntatic equality (but nat_expr are compared using affine_map)
*)
Module ExprEq.

Definition nat_expr_eqb(a b:nat_expr):bool :=
match solve_nat_eq a b with
| nil => true
| _ => false
end.

Fixpoint seg_expr_eqb(a b:seg_expr):bool :=
match a,b with
| seg_sym a0,seg_sym b0 => sym_eqb a0 b0
| seg_concat a0 a1,seg_concat b0 b1 => seg_expr_eqb a0 b0 && seg_expr_eqb a1 b1
| seg_repeat a0 an,seg_repeat b0 bn => seg_expr_eqb a0 b0 && nat_expr_eqb an bn
| seg_var a0,seg_var b0 => (a0 =? b0)%positive
| _,_ => false
end.

Fixpoint side_expr_eqb(a b:side_expr):bool :=
match a,b with
| side_0inf,side_0inf => true
| side_var a0,side_var b0 => (a0 =? b0)%positive
| side_concat a0 a1,side_concat b0 b1 => seg_expr_eqb a0 b0 && side_expr_eqb a1 b1
| _,_ => false
end.

Definition config_expr_eqb(a b:config_expr):bool :=
let '(l1,r1,s1,sgn1) := a in
let '(l2,r2,s2,sgn2) := b in
(q_eqb s1 s2) && (dir_eqb sgn1 sgn2) &&
(side_expr_eqb l1 l2) && (side_expr_eqb r1 r2).

Definition prop0_eqb(a b:prop0_expr):bool :=
match a,b with
| nat_eq a0 a1,nat_eq b0 b1 => nat_expr_eqb a0 b0 && nat_expr_eqb a1 b1
| seg_eq a0 a1,seg_eq b0 b1 => seg_expr_eqb a0 b0 && seg_expr_eqb a1 b1
| side_eq a0 a1,side_eq b0 b1 => side_expr_eqb a0 b0 && side_expr_eqb a1 b1
| config_eq a0 a1,config_eq b0 b1 => config_expr_eqb a0 b0 && config_expr_eqb a1 b1
| false_prop0,false_prop0 => true
| multistep_expr a0 a1 an,multistep_expr b0 b1 bn =>
  config_expr_eqb a0 b0 && config_expr_eqb a1 b1 && nat_expr_eqb an bn
| multistep'_expr a0 a1 an,multistep'_expr b0 b1 bn =>
  config_expr_eqb a0 b0 && config_expr_eqb a1 b1 && Bool.eqb an bn
| _,_ => false
end.

Fixpoint list_prop0_eqb(a b:list prop0_expr):bool :=
match a,b with
| nil,nil => true
| a0::a1,b0::b1 =>
  prop0_eqb a0 b0 &&
  list_prop0_eqb a1 b1
| _,_ => false
end.

Definition prop_eqb(a b:prop_expr):bool :=
let (a0,a1):=a in
let (b0,b1):=b in
list_prop0_eqb a0 b0 &&
list_prop0_eqb a1 b1.

End ExprEq.



Section allFV.

Definition S:Type := (PositiveMap.tree id_t)*positive.
Definition S0 := (PositiveMap.empty id_t,xH).
Definition add_var(s:S)(i:id_t):S :=
let (f,p):=s in
match PositiveMap.find i f with
| None => (PositiveMap.add i p f,Pos.succ p)
| Some _ => s
end.

Fixpoint nat_allFV(x:nat_expr)(s:S):S :=
match x with
| from_nat x0 => s
| nat_add a b => nat_allFV a (nat_allFV b s)
| nat_mul a b => nat_allFV a (nat_allFV b s)
| nat_var i0 => add_var s i0
| nat_ivar => s
end.

Fixpoint seg_allFV(x:seg_expr)(s:S):S :=
match x with
| seg_sym a => s
| seg_concat a b => seg_allFV a (seg_allFV b s)
| seg_repeat a n => seg_allFV a (nat_allFV n s)
| seg_var i0 => add_var s i0
end.

Fixpoint side_allFV(x:side_expr)(s:S):S :=
match x with
| side_0inf => s
| side_var i0 => add_var s i0
| side_concat a b => seg_allFV a (side_allFV b s)
end.


Definition expr_allFV(e:expr_expr):=
match e with
| existT _ nat_t x => nat_allFV x
| existT _ seg_t x => seg_allFV x
| existT _ side_t x => side_allFV x
end.


Definition config_allFV(x:config_expr)(s:S):S :=
  let '(l,r,_,_):=x in
  side_allFV l (side_allFV r s).

Definition prop0_allFV(x:prop0_expr)(s:S):S :=
match x with
| nat_eq a b => nat_allFV b (nat_allFV a s)
| seg_eq a b => seg_allFV b (seg_allFV a s)
| side_eq a b => side_allFV b (side_allFV a s)
| config_eq a b => config_allFV b (config_allFV a s)
| false_prop0 => s
| multistep_expr a b n => config_allFV a (config_allFV b (nat_allFV n s))
| multistep'_expr a b n => config_allFV a (config_allFV b s)
end.

Fixpoint list_prop0_allFV(x:list prop0_expr)(s:S):S :=
match x with
| nil => s
| h::t => prop0_allFV h (list_prop0_allFV t s)
end.

Definition prop_allFV(x:prop_expr)(s:S):S :=
let '(H,G):=x in
list_prop0_allFV H (list_prop0_allFV G s).

End allFV.

Module SimplExpr.

Definition simpl_nat x :=
  simpls_nat_expr (simpl_nat_expr_by_affine_map x).

Fixpoint simpl_seg(x:seg_expr) :=
match x with
| seg_sym a => x
| seg_concat a b => seg_concat (simpl_seg a) (simpl_seg b)
| seg_repeat a n => seg_repeat (simpl_seg a) (simpl_nat n)
| seg_var i => x
end.

Fixpoint simpl_side(x:side_expr) :=
match x with
| side_0inf => x
| side_var i => x
| side_concat a b => side_concat (simpl_seg a) (simpl_side b)
end.

Definition simpl_config(x:config_expr) :=
let '(l,r,q,d):=x in
(simpl_side l,simpl_side r,q,d).

Definition simpl_prop0(x:prop0_expr) :=
match x with
| nat_eq a b => nat_eq (simpl_nat a) (simpl_nat b)
| seg_eq a b => seg_eq (simpl_seg a) (simpl_seg b)
| side_eq a b => side_eq (simpl_side a) (simpl_side b)
| config_eq a b => config_eq (simpl_config a) (simpl_config b)
| false_prop0 => false_prop0
| multistep_expr x0 x1 n => multistep_expr (simpl_config x0) (simpl_config x1) (simpl_nat n)
| multistep'_expr x0 x1 n => multistep'_expr (simpl_config x0) (simpl_config x1) n
end.

Definition simpl_prop0_list(x:list prop0_expr) :=
map simpl_prop0 x.

Definition simpl_prop(x:prop_expr) :=
let (H,G):=x in
(simpl_prop0_list H,simpl_prop0_list G).

End SimplExpr.

Module SubstExpr.
Section subst_expr.

Hypothesis mp: id_t -> forall t:type_t, to_expr_type t.
Hypothesis mpi: nat_expr.

Fixpoint subst_nat(x:nat_expr) :=
match x with
| from_nat n => x
| nat_add a b => nat_add (subst_nat a) (subst_nat b)
| nat_mul a b => nat_mul (subst_nat a) (subst_nat b)
| nat_var i => (mp i nat_t)
| nat_ivar => mpi
end.

Fixpoint subst_seg(x:seg_expr) :=
match x with
| seg_sym a => x
| seg_concat a b => seg_concat (subst_seg a) (subst_seg b)
| seg_repeat a n => seg_repeat (subst_seg a) (subst_nat n)
| seg_var i => (mp i seg_t)
end.

Fixpoint subst_side(x:side_expr) :=
match x with
| side_0inf => x
| side_var i => (mp i side_t)
| side_concat a b => side_concat (subst_seg a) (subst_side b)
end.

Definition subst_expr(t:type_t)(x:to_expr_type t):to_expr_type t.
destruct t.
- apply (subst_nat x).
- apply (subst_seg x).
- apply (subst_side x).
Defined.

Definition subst_config(x:config_expr) :=
let '(l,r,q,d):=x in
(subst_side l,subst_side r,q,d).

Definition subst_prop0(x:prop0_expr) :=
match x with
| nat_eq a b => nat_eq (subst_nat a) (subst_nat b)
| seg_eq a b => seg_eq (subst_seg a) (subst_seg b)
| side_eq a b => side_eq (subst_side a) (subst_side b)
| config_eq a b => config_eq (subst_config a) (subst_config b)
| false_prop0 => false_prop0
| multistep_expr x0 x1 n => multistep_expr (subst_config x0) (subst_config x1) (subst_nat n)
| multistep'_expr x0 x1 n => multistep'_expr (subst_config x0) (subst_config x1) n
end.

Definition subst_prop0_list(x:list prop0_expr) :=
map subst_prop0 x.

Definition subst_prop(x:prop_expr) :=
let (H,G):=x in
(subst_prop0_list H,subst_prop0_list G).

End subst_expr.
End SubstExpr.



Definition mk_var i t: to_expr_type t :=
match t with
| nat_t => nat_var i
| seg_t => seg_var i
| side_t => side_var i
end.

Definition lookup_var t t0 (v:to_expr_type t)(v0:to_expr_type t0):to_expr_type t0.
  destruct t,t0.
  all: try (exact v).
  all: exact v0.
Defined.


Definition subst_vars(mp:PositiveMap.tree expr_expr)(i0:id_t)(t0:type_t):to_expr_type t0 :=
  match PositiveMap.find i0 mp with
  | None => mk_var i0 t0
  | Some (existT _ t v) => lookup_var t t0 v (mk_var i0 t0)
  end.

Definition subst_identity(i0:id_t)(t0:type_t):to_expr_type t0 :=
  mk_var i0 t0.

Definition rename_var_by_add(di:id_t)(i0:id_t)(t0:type_t):to_expr_type t0 :=
  mk_var (i0+di)%positive t0.

Definition rename_var_by_sort(x:prop_expr) :=
  let (f,p):=prop_allFV x S0 in
  (SubstExpr.subst_prop (fun i t =>
    match PositiveMap.find i f with
    | None => mk_var i t
    | Some i1 => mk_var i1 t
    end) nat_ivar x,p).

Module TrySubst.
Record Config := {
  enable_subst_exgcd : bool;
  enable_eq_sym : bool;
  allowed_lhs_vars : id_t->bool;
}.

Definition config_normal:= {|
  enable_subst_exgcd := true;
  enable_eq_sym := true;
  allowed_lhs_vars := fun _ => true;
|}.

Definition config_limited(l r:id_t) := {|
  enable_subst_exgcd := false;
  enable_eq_sym := false;
  allowed_lhs_vars := fun i0 => (l<=?i0)%positive && (i0<=?r)%positive;
|}.

Section TrySubst_config.
Hypothesis cfg:Config.

(* lhs vars, rhs vars, fresh var *)
Definition subst_state:Type :=
  (PositiveMap.tree expr_expr)*(PositiveMap.tree unit)*id_t.

Definition subst1(l1:id_t)(e:expr_expr)(s:subst_state):subst_state :=
if negb (cfg.(allowed_lhs_vars) l1) then s else
let '(sl,sr,p'):=s in
match PositiveMap.find l1 sl with (* l1 not in sl *)
| Some _ => s
| None =>
  let (r1,_):=(expr_allFV e S0) in
  if PositiveMap.fold (fun k v s0 =>
    match PositiveMap.find k sl with
    | Some _ => true
    | None => s0
    end) r1 false
  then s
  else (* x in r1 -> x not in dom sl *)
    let sr':=PositiveMap.fold (fun k v s0 => PositiveMap.add k tt s0) r1 sr in (* sr += r1 *)
    match PositiveMap.find l1 sr' with
    | Some _ => s
    | None => (* l1 not in sr *)
      let sl' := PositiveMap.add l1 e sl in (* sl += (l1,e) *)
      (sl',sr,p')
    end
end.

Definition fresh_var(s:subst_state):id_t*subst_state :=
let '(sl,sr,p):=s in
(p,(sl,sr,Pos.succ p)).

Definition to_affine_1d(x:nat_expr):option (id_t*N*N) :=
match x with
| nat_var i => Some (i,1,0)
| nat_mul (nat_var i) (from_nat k) => Some (i,k,0)
| nat_add (nat_var i) (from_nat k0) => Some (i,1,k0)
| nat_add (nat_mul (nat_var i) (from_nat k)) (from_nat k0) => Some (i,k,k0)
| _ => None
end%N.

Definition find_subst_exgcd'(x y:id_t)(a b c:N)(s:subst_state):subst_state :=
  let (x',y') := exgcd a b in
  if
    (N.gcd a b =? 1)%N &&
    negb (a =? 0)%N &&
    negb (b =? 0)%N &&
    (a * x' mod b =? 1 mod b)%N &&
    (b * y' mod a =? 1 mod a)%N
  then
    let s:=
    (if (a =? 1)%N then s else
    let (i,s):=fresh_var s in
    subst1 y (make_expr_expr nat_t (nat_add (nat_mul (nat_var i) (from_nat a)) (from_nat ((a-((c*y') mod a)) mod a)))) s) in

    (if (b =? 1)%N then s else
    let (i,s):=fresh_var s in
    subst1 x (make_expr_expr nat_t (nat_add (nat_mul (nat_var i) (from_nat b)) (from_nat ((c*x') mod b)))) s)
  else
    s.

Definition find_subst_exgcd(a b:nat_expr)(s:subst_state):subst_state :=
match to_affine_1d a,to_affine_1d b with
| Some (a0,a1,a2),Some (b0,b1,b2) =>
  if (a2 =? 0)%N then
    find_subst_exgcd' a0 b0 a1 b1 b2 s
  else if (b2 =? 0)%N then
    find_subst_exgcd' b0 a0 b1 a1 a2 s
  else
    s
| _,_ => s
end.


Definition find_subst(x:prop0_expr)(s:subst_state):subst_state :=
match x with
| nat_eq (nat_var i0) b => subst1 i0 (make_expr_expr nat_t b) s
| nat_eq a b => if cfg.(enable_subst_exgcd) then find_subst_exgcd a b s else s
| seg_eq (seg_var i0) b => subst1 i0 (make_expr_expr seg_t b) s
| side_eq (side_var i0) b => subst1 i0 (make_expr_expr side_t b) s
| _ => s
end.

Definition simpl_eq(x:prop0_expr):prop0_expr :=
match x with
| nat_eq a (nat_var i0) => nat_eq (nat_var i0) a
| seg_eq a (seg_var i0) => seg_eq (seg_var i0) a
| side_eq a (side_var i0) => side_eq (side_var i0) a
| _ => x
end.

Fixpoint list_find_subst(ls:list prop0_expr)(s:subst_state):subst_state :=
match ls with
| nil => s
| h0::t =>
  let h:=(if cfg.(enable_eq_sym) then simpl_eq h0 else h0) in
  list_find_subst t (find_subst h s)
end.

Definition try_subst(x:prop_expr)(i:id_t) :=
let (H,G):=x in
let '(sl,_,p):=list_find_subst H (PositiveMap.empty _,PositiveMap.empty _,i) in
((SubstExpr.subst_prop (subst_vars sl) nat_ivar x,p),sl).

End TrySubst_config.
End TrySubst.



Definition solve_assumptions_iter_limit:nat := 16.

Fixpoint solve_assumptions(n:nat)(cfg:TrySubst.Config)(x:prop_expr)(i:id_t):option (prop_expr*_) :=
match n with
| O => None
| Datatypes.S n0 =>
  let x0:=x in
  let x:=prop_solve_eq x in
  if prop_has_false x then None else
  let '((x,i),mp0):=TrySubst.try_subst cfg x i in
  if list_prop0_eqb (fst x) nil then Some (x,mp0::nil) else
  if prop_eqb x x0 then Some (x,mp0::nil) else (* allow non-empty assumptions *)
  match solve_assumptions n0 cfg x i with
  | None => None
  | Some (x',mp0') => Some (x',mp0::mp0')
  end
end.

Definition prop_expr':Type := prop_expr*id_t.

Definition simpl_rule(x:prop_expr):prop_expr' :=
  let x:=SimplExpr.simpl_prop x in
  (rename_var_by_sort x).


Definition prop_merge(x1 x2:prop_expr)(di:id_t):prop_expr :=
let (H1,G1):=x1 in
let (H2,G2):=SubstExpr.subst_prop (rename_var_by_add di) nat_ivar x2 in
(H1++H2,G1++G2).

Definition prop_multistep'_trans(x:prop_expr): option prop_expr :=
match x with
| (H,[multistep'_expr s1 s2 n1;multistep'_expr s3 s4 n2]) => Some ((config_eq s2 s3)::H,[multistep'_expr s1 s4 (n1||n2)])
| _ => None
end.

Definition prop_multistep'_apply(x1 x2:prop_expr): option prop_expr :=
match x1,x2 with
| ([],[multistep'_expr s1 s2 n1]),([],[multistep'_expr s3 s4 n2]) =>
  if n1 || negb n2 then
    Some ([config_eq s1 s3; config_eq s2 s4],[multistep'_expr s3 s4 n2])
  else None
| _,_ => None
end.

Definition follow_rule(w1 w2:prop_expr'):option prop_expr' :=
let (x1,i1):=w1 in
let (x2,i2):=w2 in
let x:=(prop_merge x1 x2 i1) in
match prop_multistep'_trans x with
| None => None
| Some x =>
  match solve_assumptions solve_assumptions_iter_limit TrySubst.config_normal x (i1+i2+1)%positive with
  | None => None
  | Some (x,_) => Some (simpl_rule x)
  end
end.

Module FindIH.

Definition oNmin(a b:option N):option N :=
match a,b with
| Some a0,Some b0 => Some (N.min a0 b0)
| Some a0,None => a
| None,_ => b
end.

Module Visit1.
(* guess induction hypothesis *)
Section visit.

Definition visit_seg(a b ca cb:seg_expr):option (seg_expr*seg_expr*(list prop0_expr)) :=
if seg_expr_eqb a b then Some (a,a,[]) else
match a,b,ca,cb with
| seg_repeat a0 an,seg_repeat b0 bn,seg_repeat ca0 (from_nat can),seg_repeat cb0 (from_nat cbn) =>
  if seg_expr_eqb a0 b0 && seg_expr_eqb a0 ca0 && seg_expr_eqb a0 cb0 then
    if (can <=? cbn)%N then (* inc *)
      let d := (cbn-can)%N in
      let an' := (nat_add an (nat_mul (nat_ivar) (from_nat d))) in
      Some (seg_repeat a0 an,seg_repeat a0 an',[nat_eq (nat_add an (from_nat d)) bn]) (* inc *)
    else (* dec *)
      let d := (can-cbn)%N in
      let bn' := (nat_add bn (nat_mul (nat_ivar) (from_nat d))) in
      Some (seg_repeat b0 bn',seg_repeat b0 bn,[nat_eq (nat_add bn (from_nat d)) an]) (* dec *)
  else None
| _,_,_,_ => None
end.

Fixpoint visit_side(a b ca cb:side_expr):option (side_expr*side_expr*(list prop0_expr)) :=
match a,b,ca,cb with
| side_concat a0 a1,side_concat b0 b1,side_concat ca0 ca1,side_concat cb0 cb1 =>
  match visit_seg a0 b0 ca0 cb0 with
  | None => None
  | Some (v0,v0',H0) =>
    match visit_side a1 b1 ca1 cb1 with
    | None => None
    | Some (v1,v1',H1) => Some (side_concat v0 v1,side_concat v0' v1',H0++H1)
    end
  end
| side_var a0,side_var b0,_,_ => if side_expr_eqb a b then Some (a,a,[]) else None
| side_0inf,side_0inf,side_0inf,side_0inf => Some (a,a,[])
| _,_,_,_ => None
end.

Definition visit_config(a b c0 c:config_expr) :=
let '(l1,r1,s1,sgn1):=a in
let '(l2,r2,s2,sgn2):=b in
let '(l30,r30,s30,sgn30):=c0 in
let '(l3,r3,s3,sgn3):=c in
if q_eqb s1 s2 && q_eqb s1 s30 && q_eqb s1 s3 && dir_eqb sgn1 sgn2 && dir_eqb sgn1 sgn30 && dir_eqb sgn1 sgn3 then
  match visit_side l1 l2 l30 l3 with
  | None => None
  | Some (l4,l4',Hl) =>
    match visit_side r1 r2 r30 r3 with
    | None => None
    | Some (r4,r4',Hr) => Some ((l4,r4,s1,sgn1),(l4',r4',s1,sgn1),Hl++Hr)
    end
  end
else None.

Definition visit_prop0(a:prop0_expr)(c0 c1:config_expr) :=
match a with
| multistep'_expr a0 a1 true =>
  visit_config a0 a1 c0 c1
| _ => None
end.
End visit.
End Visit1.

Module Visit2. (* guess the value that decrease to near-zero *)
Section visit.
Hypothesis n:N.

Definition visit_seg'(c:seg_expr)(p:id_t) :=
match c with
| seg_repeat c0 cn => (seg_repeat c0 (nat_var p),Pos.succ p)
| _ => (c,p)
end.

Definition visit_seg(a b ca cb:seg_expr)(p:id_t) :=
match a,b,ca,cb with
| seg_repeat a0 an,seg_repeat b0 bn,seg_repeat ca0 (from_nat can),seg_repeat cb0 (from_nat cbn) =>
  if (can <=? cbn)%N then (* inc *)
    visit_seg' cb p
  else (* dec *)
    let d := (can-cbn)%N in
    let bn' :=
    match bn with
    | from_nat x => x
    | nat_add _ (from_nat x) => x
    | _ => N0
    end in
    if ((cbn-bn')/d =? n)%N then
      (seg_repeat b0 (from_nat (((cbn-bn') mod d)+bn')%N),p) (* dec *)
    else visit_seg' cb p
| _,_,_,_ => visit_seg' cb p
end.

Fixpoint visit_side(a b c' c:side_expr)(p:id_t) :=
match a,b,c',c with
| side_concat a0 a1,side_concat b0 b1,side_concat c0' c1',side_concat c0 c1 =>
  let (x0,p):=(visit_seg a0 b0 c0' c0 p) in
  let (x1,p):=(visit_side a1 b1 c1' c1 p) in
  (side_concat x0 x1,p)
| _,_,_,_ => (side_var p,Pos.succ p)
end.

Definition visit_config(a b c' c:config_expr)(p:id_t) :=
let '(l1,r1,s1,sgn1):=a in
let '(l2,r2,s2,sgn2):=b in
let '(l3',r3',s3',sgn3'):=c' in
let '(l3,r3,s3,sgn3):=c in
let (lx,p):=visit_side l1 l2 l3' l3 p in
let (rx,p):=visit_side r1 r2 r3' r3 p in
((lx,rx,s2,sgn2),p).

Definition visit_config'(c:config_expr)(p:id_t) :=
let '(l3,r3,s3,sgn3):=c in
let (lx,p):=(side_var p,Pos.succ p) in
let (rx,p):=(side_var p,Pos.succ p) in
((lx,rx,s3,sgn3),p).

End visit.
End Visit2.

Module Visit3.
(* guess n *)

Definition visit_seg(a b ca cb:seg_expr):option N :=
match a,b,ca,cb with
| seg_repeat a0 an,seg_repeat b0 bn,seg_repeat ca0 (from_nat can),seg_repeat cb0 (from_nat cbn) =>
  if (can <=? cbn)%N then (* inc *)
    None
  else (* dec *)
    let d := (can-cbn)%N in
    let bn' :=
    match bn with
    | from_nat x => x
    | nat_add _ (from_nat x) => x
    | _ => N0
    end in
    Some (1+(cbn-bn')/d)%N (* dec *)
| _,_,_,_ => None
end.

Fixpoint visit_side(a b ca cb:side_expr):option N :=
match a,b,ca,cb with
| side_concat a0 a1,side_concat b0 b1,side_concat ca0 ca1,side_concat cb0 cb1 =>
  oNmin (visit_seg a0 b0 ca0 cb0) (visit_side a1 b1 ca1 cb1)
| _,_,_,_ => None
end.

Definition visit_config(a b c0 c:config_expr) :=
let '(l1,r1,s1,sgn1):=a in
let '(l2,r2,s2,sgn2):=b in
let '(l30,r30,s30,sgn30):=c0 in
let '(l3,r3,s3,sgn3):=c in
oNmin (visit_side l1 l2 l30 l3) (visit_side r1 r2 r30 r3).

End Visit3.


Definition find_IH(x:prop_expr)(i:id_t)(x0' x0:prop_expr):option (prop_expr'*(prop_expr')*_*option N) :=
match x,x0',x0 with
| (Hx,[a]),([],[multistep'_expr _ c' _]),([],[multistep'_expr _ c _]) =>
  match Visit1.visit_prop0 a c' c with
  | None => None
  | Some (a,b,H) =>
    match solve_assumptions solve_assumptions_iter_limit TrySubst.config_normal (H++Hx,[multistep'_expr a b false]) i with
    | Some (Hx',[multistep'_expr a b false],mp) =>
      let n := Visit3.visit_config a b c' c in
      let (b',p) :=
      match n with
      | None => Visit2.visit_config' c 1%positive
      | Some n => Visit2.visit_config n a b c' c 1%positive
      end in
      let w0 := (simpl_rule (Hx',[multistep'_expr a b false])) in
      let w1 := ([],[multistep'_expr b' b' false],p) in
      match n with
      | None =>
        match follow_rule ([],[multistep'_expr c' c' false],1%positive) w0 with
        | Some w0' => Some (simpl_rule (fst w0'),w1,mp,n)
        | None => None
        end
      | Some _ => Some (w0,w1,mp,n)
      end
    | _ => None
    end
  end
| _,_,_ => None
end.

End FindIH.




Section tm_ctx.
Hypothesis tm:TM.

Section subst_var.
Hypothesis mp:id_t->forall t:type_t, to_type t.
Hypothesis mpi:N.

Fixpoint to_nat(x:nat_expr) :=
(match x with
| from_nat n => n
| nat_add a b => (to_nat a) + (to_nat b)
| nat_mul a b => (to_nat a) * (to_nat b)
| nat_var i => (mp i nat_t)
| nat_ivar => mpi
end)%N.

Fixpoint to_seg(x:seg_expr):list Sym :=
match x with
| seg_sym a => [a]
| seg_concat a b => (to_seg a) ++ (to_seg b)
| seg_repeat a n => (to_seg a) ^^ (N.to_nat (to_nat n))
| seg_var i => (mp i seg_t)
end.

Fixpoint to_side(x:side_expr):side :=
match x with
| side_0inf => const s0
| side_var i => (mp i side_t)
| side_concat a b => to_seg a *> to_side b
end.


Definition to_expr t1 (e1:to_expr_type t1): to_type t1.
destruct t1; cbn in e1; cbn.
- apply (to_nat e1).
- apply (to_seg e1).
- apply (to_side e1).
Defined.

Definition to_config(x:config_expr) :=
let '(l,r,q,d):=x in
match d with
| L => (to_side r) <{{q}} (to_side l)
| R => (to_side l) {{q}}> (to_side r)
end.

Definition to_prop0(x:prop0_expr):Prop :=
match x with
| nat_eq a b => to_nat a = to_nat b
| seg_eq a b => to_seg a = to_seg b
| side_eq a b => to_side a = to_side b
| config_eq a b => to_config a = to_config b
| false_prop0 => False
| multistep_expr x0 x1 n => (to_config x0) -[tm]->> (N.to_nat (to_nat n)) / (to_config x1)
| multistep'_expr x0 x1 n => multistep' tm n (to_config x0) (to_config x1)
end.

Definition to_prop0_list(x:list prop0_expr):Prop :=
Forall to_prop0 x.

Definition to_prop(x:prop_expr):Prop :=
let (H,G):=x in
to_prop0_list H ->
to_prop0_list G.


Definition affine_map_to_Z(f:affine_map):Z :=
let (v1,v2):=from_affine_map f in
(Z.of_N (to_nat v1))-(Z.of_N (to_nat v2)).


Lemma affine_map_to_Z_cons x0 y0 f:
  (affine_map_to_Z ((x0,y0)::f) = (Z.of_N (to_nat x0))*y0 + (affine_map_to_Z f))%Z.
Proof.
  unfold affine_map_to_Z.
  cbn.
  destruct (from_affine_map f) as [v1 v2].
  destruct y0 as [|y0|y0]; cbn; lia.
Qed.

Lemma affine_map_upd'_spec f x u:
  let (f',t) := affine_map_upd' f x u in
  if t then (affine_map_to_Z f') = ((affine_map_to_Z f) + (Z.of_N (to_nat x)) * u)%Z
  else (affine_map_to_Z f') = (affine_map_to_Z f).
Proof.
  induction f as [|[x0 y0] f].
  1: reflexivity.
  cbn.
  destruct (affine_map_upd' f x u) as [f' t].
  destruct (nat_expr_eqb_spec x0 x).
  - subst.
    repeat rewrite affine_map_to_Z_cons.
    lia.
  - destruct t.
    + repeat rewrite affine_map_to_Z_cons.
      lia.
    + repeat rewrite affine_map_to_Z_cons.
      lia.
Qed.

Lemma affine_map_upd_spec f x u:
  affine_map_to_Z (affine_map_upd f x u) = ((affine_map_to_Z f) + (Z.of_N (to_nat x)) * u)%Z.
Proof.
  unfold affine_map_upd.
  pose proof (affine_map_upd'_spec f x u) as H.
  destruct (affine_map_upd' f x u) as [f' [|]].
  - apply H.
  - rewrite affine_map_to_Z_cons.
    lia.
Qed.

Lemma add_to_affine_map_spec a u f:
  affine_map_to_Z (add_to_affine_map a u f) =
  ((affine_map_to_Z f)+(Z.of_N (to_nat a))*u)%Z.
Proof.
  gen u f.
  induction a; intros; cbn.
  - rewrite affine_map_upd_spec.
    cbn[to_nat]. lia.
  - rewrite IHa2,IHa1.
    lia.
  - destruct a2.
    1: cbn; rewrite IHa1; lia.
    all:
      rewrite affine_map_upd_spec;
      reflexivity.
  - rewrite affine_map_upd_spec;
    reflexivity.
  - rewrite affine_map_upd_spec.
    reflexivity.
Qed.

Lemma affine_map_div_spec f g:
  g<>Z0 ->
  affine_map_divide f g ->
  (let (f0,m0) := (affine_map_div f g) in
  (affine_map_to_Z f0)*g+m0 = affine_map_to_Z f)%Z.
Proof.
  intro Hg.
  induction f as [|[x0 y0] f]; intros H; cbn.
  1: reflexivity.
  cbn in H.
  destruct (affine_map_div f g) as [f0 m0] eqn:E.
  repeat rewrite affine_map_to_Z_cons.
  destruct (nat_expr_eqb_spec x0 (from_nat 1)).
  + rewrite <-IHf. 2: tauto.
    rewrite e. change (Z.of_N (to_nat (from_nat 1))) with (1%Z).
    lia.
  + destruct H as [[y1 Ha] Hb].
    subst y0.
    rewrite Z.div_mul; auto. lia.
Qed.

Lemma from_affine_map_spec f:
  let (v1,v2):=from_affine_map f in
  (affine_map_to_Z f = Z.of_N (to_nat v1) - Z.of_N (to_nat v2))%Z.
Proof.
  induction f as [|[x0 y0] f].
  1: cbn; lia.
  cbn.
  rewrite affine_map_to_Z_cons.
  destruct (from_affine_map f) as [v1 v2].
  destruct y0 as [|y0|y0]; cbn; lia.
Qed.

Lemma from_affine_map_spec' f:
  let (v1,v2):=from_affine_map f in
  affine_map_to_Z f = Z0 <->
  to_nat v1 = to_nat v2.
Proof.
  pose proof (from_affine_map_spec f) as H.
  destruct (from_affine_map f) as [v1 v2].
  lia.
Qed.


Lemma simpl_nat_expr_spec x:
  to_nat (simpl_nat_expr x) = to_nat x.
Proof.
  destruct x.
  all: try reflexivity.
  - destruct x1.
    all: try reflexivity.
    + destruct n.
      * reflexivity.
      * cbn[simpl_nat_expr]. cbn[to_nat]. lia.
    + destruct x1_2.
      all: try reflexivity.
      cbn. lia.
  - destruct x1,x2; cbn.
    all: try reflexivity.
    all: destruct n as [|[n|n|]];
    try reflexivity.
    all: try destruct n0 as [|[n0|n0|]];
    try reflexivity.
    all: cbn[to_nat]; lia.
Qed.

Lemma simpls_nat_expr_spec x:
  to_nat (simpls_nat_expr x) = to_nat x.
Proof.
  induction x.
  all: try reflexivity.
  - cbn[simpls_nat_expr].
    repeat rewrite simpl_nat_expr_spec.
    cbn.
    congruence.
  - cbn[simpls_nat_expr].
    repeat rewrite simpl_nat_expr_spec.
    cbn.
    congruence.
Qed.

Lemma simpl_nat_expr_by_affine_map_spec x:
  to_nat (simpl_nat_expr_by_affine_map x) = to_nat x.
Proof.
  unfold simpl_nat_expr_by_affine_map.
  pose proof (from_affine_map_spec (add_to_affine_map x 1 [])) as H.
  destruct (from_affine_map (add_to_affine_map x 1 [])) as [v1 v2].
  destruct (nat_expr_eqb_spec v2 (from_nat 0)).
  2: reflexivity.
  subst v2.
  rewrite add_to_affine_map_spec in H.
  cbn in H.
  lia.
Qed.

Lemma list_prop0_from_affine_map_spec f:
  to_prop0_list (list_prop0_from_affine_map f) ->
  affine_map_to_Z f = Z0.
Proof.
  unfold list_prop0_from_affine_map.
  intro H.
  pose proof (from_affine_map_spec f) as H0.
  remember (from_affine_map f) as v.
  assert (let (v1,v2):=v in to_nat v1 = to_nat v2) as H'. {
    destruct v as [v1 v2].
    destruct (nat_expr_eqb_spec v1 v2).
    - congruence.
    - unfold to_prop0_list in H.
      rewrite Forall_cons_iff in H.
      cbn in H.
      repeat rewrite simpls_nat_expr_spec in H.
      tauto.
  }
  destruct v as [v1 v2].
  lia.
Qed.

Lemma from_affine_map_simpl_div_spec f:
  to_prop0_list (from_affine_map_simpl_div f) ->
  affine_map_to_Z f = Z0.
Proof.
  unfold from_affine_map_simpl_div.
  intro H.
  destruct (Z.ltb_spec 1 (affine_map_gcd f)).
  2: apply list_prop0_from_affine_map_spec,H.
  pose proof (affine_map_gcd_spec f).
  remember (affine_map_gcd f) as g.
  pose proof (affine_map_div_spec f g).
  destruct (affine_map_div f g) as [f0 g0].
  destruct (Z.eqb_spec g0 0).
  - rewrite <-H2.
    + rewrite list_prop0_from_affine_map_spec; auto.
    + lia.
    + tauto.
  - destruct (Z.eqb (g0 mod g) 0).
    1: apply list_prop0_from_affine_map_spec,H.
    unfold to_prop0_list in H.
    rewrite Forall_cons_iff in H.
    cbn in H. tauto.
Qed.

Lemma solve_nat_eq_spec a b:
  to_prop0_list (solve_nat_eq a b) ->
  to_prop0 (nat_eq a b).
Proof.
  cbn.
  intro E.
  unfold solve_nat_eq in E.
  pose proof (from_affine_map_simpl_div_spec _ E) as H'.
  repeat rewrite add_to_affine_map_spec in H'.
  cbn in H'. lia.
Qed.

Lemma solve_seg_eq_spec a b:
  to_prop0_list (solve_seg_eq a b) ->
  to_prop0 (seg_eq a b).
Proof.
  cbn.
  gen b.
  induction a; intros b E; destruct b; unfold to_prop0_list in E; cbn; cbn in E.
  all: repeat (rewrite Forall_cons_iff in E; cbn in E).
  all: try tauto.
  - destruct (sym_eqb_spec a a0); try congruence.
    repeat rewrite Forall_cons_iff in E.
    cbn in E.
    tauto.
  - rewrite Forall_app in E.
    rewrite (IHa1 b1). 2: tauto.
    rewrite (IHa2 b2). 2: tauto.
    reflexivity.
  - rewrite Forall_app in E.
    rewrite (IHa b). 2: tauto.
    rewrite (solve_nat_eq_spec n n0). 2: tauto.
    reflexivity.
  - destruct (Pos.eqb_spec i i0).
    + congruence.
    + rewrite Forall_cons_iff in E.
      cbn in E.
      tauto.
Qed.

Lemma solve_side_eq_spec a b:
  to_prop0_list (solve_side_eq a b) ->
  to_prop0 (side_eq a b).
Proof.
  gen b.
  induction a; intros b E; destruct b; unfold to_prop0_list in E; cbn; cbn in E.
  all: repeat (rewrite Forall_cons_iff in E; cbn in E).
  all: try tauto.
  - destruct (Pos.eqb_spec i i0).
    + congruence.
    + rewrite Forall_cons_iff in E.
      cbn in E.
      tauto.
  - rewrite Forall_app in E.
    rewrite (IHa b). 2: tauto.
    rewrite (solve_seg_eq_spec a a1). 2: tauto.
    reflexivity.
Qed.

Lemma solve_config_eq_spec a b:
  to_prop0_list (solve_config_eq a b) ->
  to_prop0 (config_eq a b).
Proof.
  destruct a as [[[l1 r1] s1] d1].
  destruct b as [[[l2 r2] s2] d2].
  cbn.
  destruct (q_eqb_spec s1 s2).
  - destruct (dir_eqb_spec d1 d2).
    + subst.
      unfold to_prop0_list.
      rewrite Forall_app.
      intros [Ha Hb].
      pose proof (solve_side_eq_spec l1 l2 Ha) as H1.
      pose proof (solve_side_eq_spec r1 r2 Hb) as H2.
      cbn in H1,H2.
      rewrite H1,H2.
      congruence.
    + unfold to_prop0_list; cbn; rewrite Forall_cons_iff; cbn; tauto.
  - unfold to_prop0_list; cbn; rewrite Forall_cons_iff; cbn; tauto.
Qed.

Lemma solve_eq_spec x:
  to_prop0_list (solve_eq x) ->
  to_prop0 x.
Proof.
  destruct x; cbn.
  - apply solve_nat_eq_spec.
  - apply solve_seg_eq_spec.
  - apply solve_side_eq_spec.
  - apply solve_config_eq_spec.
  - unfold to_prop0_list.
    rewrite Forall_cons_iff; cbn; tauto.
  - unfold to_prop0_list.
    rewrite Forall_cons_iff; cbn; tauto.
  - unfold to_prop0_list.
    rewrite Forall_cons_iff; cbn; tauto.
Qed.


Lemma solve_eqs_spec x:
  to_prop0_list (solve_eqs x) ->
  to_prop0_list x.
Proof.
  induction x; cbn.
  1: tauto.
  unfold to_prop0_list.
  rewrite Forall_app.
  rewrite Forall_cons_iff.
  pose proof (solve_eq_spec a).
  tauto.
Qed.

Lemma has_false_spec x:
  has_false x = true ->
  to_prop0_list x ->
  False.
Proof.
  induction x.
  - cbn. congruence.
  - cbn.
    destruct a; cbn.
    all: unfold to_prop0_list.
    all: unfold to_prop0_list in IHx.
    all: rewrite Forall_cons_iff.
    all: tauto.
Qed.





Section ExprEq_spec.
Import ExprEq.

Lemma ExprEq_nat_spec a b:
  nat_expr_eqb a b = true ->
  to_nat a = to_nat b.
Proof.
  unfold nat_expr_eqb.
  pose proof (solve_nat_eq_spec a b).
  destruct (solve_nat_eq a b).
  2: congruence.
  intros _.
  apply H.
  constructor.
Qed.

Lemma ExprEq_seg_spec a b:
  seg_expr_eqb a b = true ->
  to_seg a = to_seg b.
Proof.
  gen b.
  induction a; intros b; destruct b; cbn; try congruence;
  repeat rewrite and_true_iff.
  - destruct (sym_eqb_spec a a0); congruence.
  - intros [H1 H2].
    erewrite IHa1; eauto.
    erewrite IHa2; eauto.
  - intros [H1 H2].
    erewrite IHa; eauto.
    erewrite ExprEq_nat_spec; eauto.
  - destruct (Pos.eqb_spec i i0); congruence.
Qed.

Lemma ExprEq_side_spec a b:
  side_expr_eqb a b = true ->
  to_side a = to_side b.
Proof.
  gen b.
  induction a; intros b; destruct b; cbn; try congruence;
  repeat rewrite and_true_iff.
  - destruct (Pos.eqb_spec i i0); congruence.
  - intros [H1 H2].
    erewrite IHa; eauto.
    erewrite ExprEq_seg_spec; eauto.
Qed.

Lemma ExprEq_config_spec a b:
  config_expr_eqb a b = true ->
  to_config a = to_config b.
Proof.
  destruct a as [[[l1 r1] s1] sgn1].
  destruct b as [[[l2 r2] s2] sgn2].
  cbn.
  repeat rewrite and_true_iff.
  intros [[[H0 H1] H2] H3].
  rewrite (ExprEq_side_spec l1 l2); auto.
  rewrite (ExprEq_side_spec r1 r2); auto.
  destruct (q_eqb_spec s1 s2); try congruence.
  destruct (dir_eqb_spec sgn1 sgn2); try congruence.
  subst. reflexivity.
Qed.

Lemma ExprEq_prop0_spec a b:
  prop0_eqb a b = true ->
  to_prop0 a = to_prop0 b.
Proof.
  destruct a,b; cbn;
  repeat rewrite and_true_iff;
  try congruence.
  - intros [H1 H2].
    rewrite (ExprEq_nat_spec a a0); auto.
    rewrite (ExprEq_nat_spec b0 b); auto.
  - intros [H1 H2].
    rewrite (ExprEq_seg_spec a a0); auto.
    rewrite (ExprEq_seg_spec b0 b); auto.
  - intros [H1 H2].
    rewrite (ExprEq_side_spec a a0); auto.
    rewrite (ExprEq_side_spec b0 b); auto.
  - intros [H1 H2].
    rewrite (ExprEq_config_spec a a0); auto.
    rewrite (ExprEq_config_spec b0 b); auto.
  - intros [[H1 H2] H3].
    rewrite (ExprEq_config_spec a a0); auto.
    rewrite (ExprEq_config_spec b0 b); auto.
    rewrite (ExprEq_nat_spec n n0); auto.
  - intros [[H1 H2] H3].
    rewrite (ExprEq_config_spec a a0); auto.
    rewrite (ExprEq_config_spec b0 b); auto.
    destruct (Bool.eqb_spec n n0); congruence.
Qed.

Lemma ExprEq_list_prop0_spec a b:
  list_prop0_eqb a b = true ->
  to_prop0_list a <-> to_prop0_list b.
Proof.
  unfold to_prop0_list.
  gen b.
  induction a as [|a0 a]; intros [|b0 b]; cbn; try congruence;
  repeat rewrite and_true_iff.
  1: tauto.
  intros [H1 H2].
  repeat rewrite Forall_cons_iff.
  rewrite (ExprEq_prop0_spec a0 b0); try tauto.
  rewrite (IHa b); tauto.
Qed.

Lemma ExprEq_prop_spec a b:
  prop_eqb a b = true ->
  to_prop a <-> to_prop b.
Proof.
  destruct a as [a0 a1].
  destruct b as [b0 b1].
  cbn; try congruence;
  repeat rewrite and_true_iff.
  intros [H1 H2].
  rewrite (ExprEq_list_prop0_spec _ _ H1).
  rewrite (ExprEq_list_prop0_spec _ _ H2).
  tauto.
Qed.

End ExprEq_spec.


Section simpl_spec.
Import SimplExpr.
Lemma nat_simpl_spec x:
  to_nat (simpl_nat x) = to_nat x.
Proof.
  unfold simpl_nat.
  rewrite simpls_nat_expr_spec.
  apply simpl_nat_expr_by_affine_map_spec.
Qed.

Lemma seg_simpl_spec x:
  to_seg (simpl_seg x) = to_seg x.
Proof.
  induction x; cbn.
  all: try congruence.
  rewrite (nat_simpl_spec n).
  congruence.
Qed.

Lemma side_simpl_spec x:
  to_side (simpl_side x) = to_side x.
Proof.
  induction x; cbn.
  all: try congruence.
  rewrite seg_simpl_spec.
  congruence.
Qed.

Lemma config_simpl_spec x:
  to_config (simpl_config x) = to_config x.
Proof.
  destruct x as [[[l r] s] sgn]; cbn.
  destruct sgn;
  repeat rewrite side_simpl_spec;
  congruence.
Qed.

Lemma prop0_simpl_spec x:
  to_prop0 (simpl_prop0 x) = to_prop0 x.
Proof.
  destruct x; cbn.
  all: repeat rewrite nat_simpl_spec.
  all: repeat rewrite seg_simpl_spec.
  all: repeat rewrite side_simpl_spec.
  all: repeat rewrite config_simpl_spec.
  all: try congruence.
Qed.

Lemma list_prop0_simpl_spec x:
  to_prop0_list (simpl_prop0_list x) <-> to_prop0_list x.
Proof.
  unfold to_prop0_list.
  induction x; cbn.
  - repeat rewrite Forall_nil_iff; tauto.
  - repeat rewrite Forall_cons_iff.
    rewrite prop0_simpl_spec; tauto.
Qed.

Lemma prop_simpl_spec x:
  to_prop (simpl_prop x) <-> to_prop x.
Proof.
  destruct x as [x0 x1]; cbn.
  repeat rewrite list_prop0_simpl_spec.
  tauto.
Qed.

End simpl_spec.

End subst_var.



Section subst_spec.
Import SubstExpr.
Hypothesis mp':id_t->forall t, to_type t.
Hypothesis mpi':N.
Hypothesis mp0:id_t->forall t, to_expr_type t.
Hypothesis mpi0:nat_expr.
Definition mp(i:id_t) t: to_type t := (to_expr mp' mpi' t (mp0 i t)).
Definition mpi:N := to_expr mp' mpi' nat_t mpi0.

Lemma nat_subst_spec x:
  to_nat mp' mpi' (subst_nat mp0 mpi0 x) = to_nat mp mpi x.
Proof.
  induction x.
  - reflexivity.
  - cbn.
    rewrite IHx1,IHx2.
    reflexivity.
  - cbn.
    rewrite IHx1,IHx2.
    reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma seg_subst_spec x:
  to_seg mp' mpi' (subst_seg mp0 mpi0 x) = to_seg mp mpi x.
Proof.
  induction x.
  - reflexivity.
  - cbn.
    rewrite IHx1,IHx2.
    reflexivity.
  - cbn.
    rewrite IHx,nat_subst_spec.
    reflexivity.
  - reflexivity.
Qed.

Lemma side_subst_spec x:
  to_side mp' mpi' (subst_side mp0 mpi0 x) = to_side mp mpi x.
Proof.
  induction x.
  - reflexivity.
  - reflexivity.
  - cbn.
    rewrite IHx,seg_subst_spec.
    reflexivity.
Qed.

Lemma config_subst_spec x:
  to_config mp' mpi' (subst_config mp0 mpi0 x) = to_config mp mpi x.
Proof.
  destruct x as [[[l r] s] sgn].
  cbn.
  destruct sgn;
  repeat rewrite side_subst_spec;
  reflexivity.
Qed.

Lemma prop0_subst_spec x:
  to_prop0 mp' mpi' (subst_prop0 mp0 mpi0 x) = to_prop0 mp mpi x.
Proof.
  destruct x; cbn.
  - repeat rewrite nat_subst_spec.
    reflexivity.
  - repeat rewrite seg_subst_spec.
    reflexivity.
  - repeat rewrite side_subst_spec.
    reflexivity.
  - repeat rewrite config_subst_spec.
    reflexivity.
  - reflexivity.
  - repeat rewrite config_subst_spec.
    repeat rewrite nat_subst_spec.
    reflexivity.
  - repeat rewrite config_subst_spec.
    reflexivity.
Qed.

Lemma prop0_list_subst_spec x:
  to_prop0_list mp' mpi' (subst_prop0_list mp0 mpi0 x) <-> to_prop0_list mp mpi x.
Proof.
  unfold to_prop0_list.
  induction x; cbn.
  - repeat rewrite Forall_nil_iff; tauto.
  - repeat rewrite Forall_cons_iff.
    rewrite prop0_subst_spec.
    tauto.
Qed.

Lemma prop_subst_spec x:
  to_prop mp' mpi' (subst_prop mp0 mpi0 x) <-> to_prop mp mpi x.
Proof.
  destruct x; cbn.
  repeat rewrite prop0_list_subst_spec.
  tauto.
Qed.

End subst_spec.






Lemma multistep'_trans n1 n2 s1 s2 s3:
  multistep' tm n1 s1 s2 ->
  multistep' tm n2 s2 s3 ->
  multistep' tm (n1||n2) s1 s3.
Proof.
  unfold multistep'.
  destruct n1,n2; cbn.
  - apply progress_trans.
  - apply progress_evstep_trans.
  - apply evstep_progress_trans.
  - apply evstep_trans.
Qed.










Definition match_prop(x1 x2:prop_expr):option prop_expr :=
match x1,x2 with
| ([],[multistep'_expr s1 s2 n1]),([],[multistep'_expr s1' s2' n1']) =>
  Some ([config_eq s1 s1';config_eq s2 s2'],[])
| _,_ => None
end.

(*
  substitute variables in w1,
  then prove w1 <-> w2 by ExprEq.prop_eqb

  (forall x, w1(x)) ->
  (forall x, w1(f(x)) <-> w2(x)) ->
  (forall x, w2(x))
*)
Definition subst_for_apply(w1 w2:prop_expr'):option _:=
let (x1,i1):=w1 in
let (x2,i2):=w2 in
let x1' := SubstExpr.subst_prop (rename_var_by_add i2) nat_ivar x1 in
match match_prop x1' x2 with
| None => None
| Some x3 =>
  match solve_assumptions solve_assumptions_iter_limit (TrySubst.config_limited i2 (i1+i2)%positive) x3 (i1+i2+1)%positive with
  | None => None
  | Some (x,mp0s) =>
    let mp0 := List.fold_left
      (fun mp0s mp0 => PositiveMap.fold (fun k v f => PositiveMap.add (k-i2)%positive v f) mp0 mp0s)
      mp0s (PositiveMap.empty _) in
      Some mp0
  end
end.

Definition solve_apply(w1 w2:prop_expr'):bool :=
match subst_for_apply w1 w2 with
| None => false
| Some mp0 =>
  let x1' := (SubstExpr.subst_prop (subst_vars mp0) nat_ivar (fst w1)) in
  ExprEq.prop_eqb x1' (fst w2)
end.


(*
  prove w by induction,
  prove base case by wO,
  prove induction step by "follow wS; follow IH; finish"
*)
Definition solve_ind(wO wS w:prop_expr'):bool :=
match follow_rule w wS with
| None => false
| Some w' =>
  solve_apply wO ((SubstExpr.subst_prop subst_identity (from_nat 0) (fst w)),(snd w)) &&
  solve_apply w' ((SubstExpr.subst_prop subst_identity (nat_add nat_ivar (from_nat 1)) (fst w)),(snd w))
end.

Definition step0_refl s sgn:prop_expr' :=
  let l:=side_var 1%positive in
  let r:=side_var 2%positive in
  (([],[multistep'_expr (l,r,s,sgn) (l,r,s,sgn) false]),
  3%positive).

Definition get_config_r(x:prop_expr') :=
let '((H,G),i):=x in
match G with
| (multistep'_expr a b n)::_ => Some b
| _ => None
end.

Definition find_step0_refl(x:prop_expr'):option prop_expr' :=
match get_config_r x with
| Some (_,_,s,sgn) => Some (step0_refl s sgn)
| None => None
end.

Definition step1_to_step0(x:prop_expr'):prop_expr' :=
match x with
| (H,(multistep'_expr a b true)::G,i) =>
  (H,(multistep'_expr a b false)::G,i)
| _ => x
end.

Definition remove_ivar(x:prop_expr'):prop_expr' :=
let (x,i):=x in
let x:=SubstExpr.subst_prop subst_identity (nat_var i) x in
simpl_rule x.

Definition specialize_ivar(x:prop_expr')(n:N):prop_expr' :=
let (x,i):=x in
let x:=SubstExpr.subst_prop subst_identity (from_nat n) x in
simpl_rule x.

Fixpoint subst_list_map(mp:list (PositiveMap.tree expr_expr))(i:id_t)(t:type_t):to_expr_type t :=
match mp with
| nil => mk_var i t
| mp0::mp =>
  SubstExpr.subst_expr (subst_list_map mp) nat_ivar t (subst_vars mp0 i t)
end.


Definition subst_ind_S(w:prop_expr') (mp:list (PositiveMap.tree expr_expr)):prop_expr' :=
  let w1 := step1_to_step0 w in
  (SubstExpr.subst_prop (subst_list_map mp) nat_ivar (fst w1),snd w1).

(*
  find accelerate rule w1^n, that can be used after w0
*)
Definition try_ind(w1 w0' w0:prop_expr'):option (prop_expr'*prop_expr') :=
let (x1,i1):=w1 in
match FindIH.find_IH x1 i1 (fst w0') (fst w0) with
| Some (w2,x3,mp,n) =>
  match (find_step0_refl w1) with
  | None => None
  | Some w10 =>
    let w1' := subst_ind_S w1 mp in
    if solve_ind w10 w1' w2 then
      match n with
      | Some n =>
        if solve_apply w10 x3 then
          match follow_rule w2 x3 with
          | None => None
          | Some w2 =>
            match follow_rule w0' (specialize_ivar w2 n) with
            | None => None
            | Some w0 => Some (remove_ivar w2,w0)
            end
          end
        else None
      | None =>
        match follow_rule w0' (remove_ivar w2) with
        | None => None
        | Some w0 => Some (remove_ivar w2,w0)
        end
      end
    else None
  end
| _ => None
end.

Definition multistep'_for_ind(w1:prop_expr'):prop_expr' :=
match w1 with
| ((H,multistep'_expr a b true::G),i) => ((H,multistep'_expr a b false::G),i)
| _ => w1
end.


Section ivar.
Hypothesis mpi:N.
Definition to_prop'' x :=
  forall mp, to_prop mp mpi x.

Opaque solve_assumptions_iter_limit.

Lemma subst_spec x mp0:
  to_prop'' x ->
  to_prop'' (SubstExpr.subst_prop mp0 nat_ivar x).
Proof.
  intros H mp'.
  rewrite prop_subst_spec.
  apply H.
Qed.

Lemma prop_merge_spec x1 x2 di:
  to_prop'' x1 ->
  to_prop'' x2 ->
  to_prop'' (prop_merge x1 x2 di).
Proof.
  pose proof (subst_spec x2) as H.
  gen H.
  unfold to_prop''.
  unfold prop_merge.
  destruct x1 as [H1 G1].
  destruct x2 as [H2 G2].
  cbn.
  unfold to_prop0_list.
  intros H Hx1 Hx2 mp.
  repeat rewrite Forall_app.
  intros.
  split.
  - apply Hx1; tauto.
  - apply H; tauto.
Qed.

Lemma prop_multistep'_trans_spec x:
match prop_multistep'_trans x with
| None => True
| Some x' => to_prop'' x -> to_prop'' x'
end.
Proof.
  destruct x as [H' G].
  destruct G as [|G0 G]; cbn; trivial.
  destruct G0; cbn; trivial.
  destruct G as [|G0 G]; cbn; trivial.
  destruct G0; cbn; trivial.
  destruct G as [|G0 G]; cbn; trivial.
  unfold to_prop''.
  cbn.
  unfold to_prop0_list.
  intros H mp.
  specialize (H mp).
  gen H.
  repeat rewrite Forall_cons_iff.
  repeat rewrite Forall_nil_iff.
  cbn.
  intros H [H0 H1].
  rewrite H0 in H.
  split; trivial.
  destruct (H H1) as [Ha [Hb _]].
  eapply multistep'_trans; eauto.
Qed.

Lemma prop_solve_eq_spec x:
  to_prop'' x ->
  to_prop'' (prop_solve_eq x).
Proof.
  destruct x as [x0 x1].
  unfold to_prop''.
  intros H mp.
  cbn.
  specialize (H mp).
  cbn in H.
  pose proof (solve_eqs_spec mp mpi x0).
  tauto.
Qed.


Lemma try_subst_spec cfg x i:
  let '((x',i'),_):=(TrySubst.try_subst cfg x i) in
  (to_prop'' x) -> (to_prop'' x').
Proof.
  destruct x as [H G].
  cbn.
  destruct (TrySubst.list_find_subst cfg H (PositiveMap.empty expr_expr, PositiveMap.empty unit, i)) as [[sl _] _].
  intros H0.
  apply (subst_spec (H,G)),H0.
Qed.

Lemma solve_assumptions_spec n cfg x i:
to_prop'' x ->
match solve_assumptions n cfg x i with
| None => True
| Some (x',_) => to_prop'' x'
end.
Proof.
  gen x i.
  induction n; intros x i H.
  1: cbn; trivial.
  cbn.
  destruct (prop_has_false (prop_solve_eq x)).
  1: trivial.
  pose proof (prop_solve_eq_spec x H) as H0.
  pose proof (try_subst_spec cfg (prop_solve_eq x) i) as H1.
  destruct (TrySubst.try_subst cfg (prop_solve_eq x) i) as [[x0 i0] mp0].
  specialize (H1 H0).
  destruct (list_prop0_eqb (fst x0) []).
  1: tauto.
  destruct (prop_eqb x0 x).
  1: trivial.
  specialize (IHn x0 i0 H1).
  destruct (solve_assumptions n cfg x0 i0) as [[]|]; trivial.
Qed.

Lemma rename_var_by_sort_spec x:
  to_prop'' x ->
  to_prop'' (fst (rename_var_by_sort x)).
Proof.
  unfold rename_var_by_sort.
  destruct (prop_allFV x S0) as [f p].
  cbn.
  apply subst_spec.
Qed.

Lemma prop_simpl_spec' x:
  to_prop'' x -> to_prop'' (SimplExpr.simpl_prop x).
Proof.
  unfold to_prop''.
  intros H mp.
  rewrite prop_simpl_spec.
  apply H.
Qed.

Lemma simpl_rule_spec x:
  to_prop'' x ->
  to_prop'' (fst (simpl_rule x)).
Proof.
  intro H3.
  apply rename_var_by_sort_spec.
  apply prop_simpl_spec'.
  apply H3.
Qed.

Lemma follow_rule_spec w1 w2:
to_prop'' (fst w1) ->
to_prop'' (fst w2) ->
match follow_rule w1 w2 with
| None => True
| Some w =>
  to_prop'' (fst w)
end.
Proof.
  destruct w1 as [x1 i1].
  destruct w2 as [x2 i2].
  cbn.
  intros H1 H2.
  pose proof (prop_merge_spec x1 x2 i1 H1 H2) as H.
  destruct_spec prop_multistep'_trans_spec. 2: tauto.
  destruct_spec solve_assumptions_spec; trivial.
  destruct p0.
  apply simpl_rule_spec. tauto.
Qed.

Transparent solve_assumptions_iter_limit.




Lemma solve_apply_spec w1 w2:
  to_prop'' (fst w1) ->
  solve_apply w1 w2 = true ->
  to_prop'' (fst w2).
Proof.
  unfold to_prop'',solve_apply.
  intros H H0 mp.
  destruct (subst_for_apply w1 w2); try congruence.
  rewrite <-ExprEq_prop_spec.
  2: apply H0.
  apply subst_spec.
  unfold to_prop''.
  apply H.
Qed.

End ivar.



Section fext.
Hypothesis mp mp': (id_t -> forall t : type_t, to_type t).
Hypothesis mpi: N.
Hypothesis mp_eq: forall i t, mp i t = mp' i t.

Lemma to_nat_fext x:
  to_nat mp mpi x = to_nat mp' mpi x.
Proof.
  induction x; cbn.
  all: congruence.
Qed.

Lemma to_seg_fext x:
  to_seg mp mpi x = to_seg mp' mpi x.
Proof.
  induction x; cbn.
  all: repeat rewrite to_nat_fext; congruence.
Qed.

Lemma to_side_fext x:
  to_side mp mpi x = to_side mp' mpi x.
Proof.
  induction x; cbn.
  all: repeat rewrite to_seg_fext; repeat rewrite to_nat_fext; congruence.
Qed.

Lemma to_config_fext x:
  to_config mp mpi x = to_config mp' mpi x.
Proof.
  destruct x as [[[l r] s] sgn]; cbn.
  repeat rewrite to_side_fext.
  reflexivity.
Qed.

Lemma to_prop0_fext x:
  to_prop0 mp mpi x = to_prop0 mp' mpi x.
Proof.
  destruct x; cbn.
  all: repeat rewrite to_nat_fext.
  all: repeat rewrite to_seg_fext.
  all: repeat rewrite to_side_fext.
  all: repeat rewrite to_config_fext.
  all: congruence.
Qed.

Lemma to_prop0_list_fext x:
  to_prop0_list mp mpi x <-> to_prop0_list mp' mpi x.
Proof.
  unfold to_prop0_list.
  induction x; cbn.
  all: repeat rewrite Forall_nil_iff.
  all: repeat rewrite Forall_cons_iff.
  all: repeat rewrite to_prop0_fext.
  all: tauto.
Qed.

Lemma to_prop_fext x:
  to_prop mp mpi x <-> to_prop mp' mpi x.
Proof.
  destruct x as [H G]. cbn.
  repeat rewrite to_prop0_list_fext.
  tauto.
Qed.
End fext.

Definition to_prop' x :=
  forall mpi, to_prop'' mpi x.

Lemma follow_rule_spec' w1 w2:
  to_prop' (fst w1) ->
  to_prop' (fst w2) ->
  match follow_rule w1 w2 with
  | Some w => to_prop' (fst w)
  | None => True
  end.
Proof.
  intros H1 H2.
  destruct (follow_rule w1 w2) eqn:E; trivial.
  intros mpi.
  pose proof (follow_rule_spec mpi w1 w2) as H.
  rewrite E in H.
  apply H.
  - apply H1.
  - apply H2.
Qed.

Lemma subst_ivar_spec w n n0:
  to_prop'' n (SubstExpr.subst_prop subst_identity n0 w) ->
  forall mp, to_prop mp (to_nat mp n n0) w.
Proof.
  intros H mp.
  specialize (H mp).
  rewrite (prop_subst_spec) in H.
  cbn in H.
  unfold subst_identity in H.
  unfold tm_ctx.mp in H.
  erewrite to_prop_fext.
  - apply H.
  - intros.
    destruct t;
    reflexivity.
Qed.

Lemma solve_ind_spec (wO wS w:prop_expr'):
  (to_prop' (fst wO)) ->
  (to_prop' (fst wS)) ->
  solve_ind wO wS w = true ->
  (to_prop' (fst w)).
Proof.
  intros HO HS H n.
  unfold solve_ind in H.
  induction n using N.peano_ind; intros.
  - eassert (forall i:N, _) as X. {
      intro i.
      pose proof (follow_rule_spec i w wS) as H0.
      destruct (follow_rule w wS) as [w'|]; try congruence.
      rewrite and_true_iff in H.
      destruct H as [Ha Hb].
      eapply (solve_apply_spec i wO _ (HO i) Ha).
    }
    cbn in X.
    intro mp.
    apply (subst_ivar_spec _ _ _ (X N0) mp).
  - eassert (_) as X. {
      pose proof (follow_rule_spec n w wS) as H0.
      destruct (follow_rule w wS) as [w'|]; try congruence.
      rewrite and_true_iff in H.
      destruct H as [Ha Hb].
      eapply (solve_apply_spec n w' _ _ Hb).
    Unshelve.
      apply (H0).
      - apply IHn.
      - apply HS.
    }
    cbn in X.
    intro mp.
    replace (N.succ n) with (n+1)%N by lia.
    apply (subst_ivar_spec _ _ _ X mp).
Qed.





Lemma remove_ivar_spec x:
  to_prop' (fst x) ->
  to_prop' (fst (remove_ivar x)).
Proof.
  destruct x as [x0 i]; cbn.
  intros H n.
  apply simpl_rule_spec.
  intros mp.
  rewrite prop_subst_spec.
  rewrite to_prop_fext.
  1: apply (H _ mp).
  intros i0 t.
  destruct t;
  reflexivity.
Qed.

Lemma specialize_ivar_spec x n:
  to_prop' (fst x) ->
  to_prop' (fst (specialize_ivar x n)).
Proof.
  destruct x as [x0 i]; cbn.
  intros H n0.
  apply simpl_rule_spec.
  intros mp.
  rewrite prop_subst_spec.
  rewrite to_prop_fext.
  1: apply (H _ mp).
  intros i0 t.
  destruct t;
  reflexivity.
Qed.

Lemma step0_refl_spec s sgn:
  to_prop' (fst (step0_refl s sgn)).
Proof.
  intros mp mpi.
  cbn.
  unfold to_prop0_list.
  repeat rewrite Forall_cons_iff.
  repeat rewrite Forall_nil_iff.
  cbn.
  destruct sgn; cbn;
  intro; split; trivial.
Qed.

Lemma find_step0_refl_spec x:
  match find_step0_refl x with
  | None => True
  | Some x0 => to_prop' (fst x0)
  end.
Proof.
  unfold find_step0_refl.
  destruct (get_config_r x) as [[[[l r] s] sgn]|]; trivial.
  apply step0_refl_spec.
Qed.

Lemma multistep'_for_ind_spec w:
  to_prop' (fst w) ->
  to_prop' (fst (multistep'_for_ind w)).
Proof.
  destruct w as [[H G] i].
  destruct G as [|G0 G]; cbn.
  1: tauto.
  destruct G0; cbn; try tauto.
  destruct n; cbn; try tauto.
  intros H0 mpi mp.
  specialize (H0 mpi mp).
  gen H0.
  cbn.
  unfold to_prop0_list.
  repeat rewrite Forall_cons_iff.
  cbn.
  intros H0 H1.
  specialize (H0 H1).
  split; try tauto.
  apply progress_evstep. tauto.
Qed.

Lemma step1_to_step0_spec w:
  to_prop' (fst w) ->
  to_prop' (fst (step1_to_step0 w)).
Proof.
  destruct w as [[H G] i].
  destruct G as [|[] G]; try tauto.
  destruct n; try tauto.
  cbn.
  unfold to_prop'.
  intros H0 mpi mp.
  specialize (H0 mpi mp).
  gen H0.
  unfold to_prop,to_prop0_list.
  repeat rewrite Forall_cons_iff.
  intros H1 H2.
  specialize (H1 H2).
  destruct H1 as [H1 H3].
  split; try tauto.
  gen H1.
  cbn.
  apply progress_evstep.
Qed.

Lemma subst_ind_S_spec w mp:
  to_prop' (fst w) ->
  to_prop' (fst (subst_ind_S w mp)).
Proof.
  intro H.
  cbn.
  intros mpi.
  apply subst_spec.
  apply step1_to_step0_spec,H.
Qed.

Lemma solve_apply_spec' w1 w2:
  to_prop' (fst w1) ->
  if solve_apply w1 w2 then to_prop' (fst w2)
  else True.
Proof.
  pose proof (fun mpi => solve_apply_spec mpi w1 w2).
  destruct (solve_apply w1 w2); trivial.
  intros H' mpi.
  apply H; trivial.
Qed.

Lemma try_ind_spec w1 w0' w0:
  to_prop' (fst w1) ->
  to_prop' (fst w0') ->
  match try_ind w1 w0' w0 with
  | None => True
  | Some (x,x0) => to_prop' (fst x) /\ to_prop' (fst x0)
  end.
Proof.
  intros H' H0'.
  unfold try_ind.
  destruct w1 as [x1 i1].
  destruct (FindIH.find_IH x1 i1 (fst w0') (fst w0)) as [[[[x2 x3] mp] n]|]; trivial.
  destruct_spec find_step0_refl_spec; trivial.
  destruct_spec solve_ind_spec; trivial.
  assert (to_prop' (fst x2)) as H1. {
    unfold to_prop'.
    apply H0; trivial.
    apply subst_ind_S_spec. tauto.
  }
  destruct n as [n|].
  - destruct_spec solve_apply_spec'; trivial.
    destruct_spec follow_rule_spec'; trivial.
    destruct_spec follow_rule_spec'; trivial.
    split.
    + apply remove_ivar_spec. tauto.
    + apply H4; try tauto.
      apply specialize_ivar_spec. tauto.
  - destruct_spec follow_rule_spec'; trivial.
    split.
    + apply remove_ivar_spec,H1.
    + apply H2; try tauto.
      apply remove_ivar_spec,H1.
Qed.









Definition to_prop0' x :=
  forall mp mpi, to_prop0 mp mpi x.

Definition side_0inf_def:=
  (side_eq
  side_0inf
  (side_concat (seg_sym s0) side_0inf),
  1%positive).

Lemma side_0inf_def_spec:
  to_prop0' (fst (side_0inf_def)).
Proof.
  unfold to_prop0'.
  intros. cbn.
  rewrite <-const_unfold.
  reflexivity.
Qed.


Fixpoint side_concat_unfold(r0:seg_expr)(r:side_expr):side_expr :=
match r0 with
| seg_concat r1 r2 =>
  side_concat r1 (side_concat_unfold r2 r)
| _ => side_concat r0 r
end.

Lemma side_concat_unfold_spec r0 r mp mpi:
  to_side mp mpi (side_concat_unfold r0 r) =
  to_seg mp mpi r0 *> to_side mp mpi r.
Proof.
  induction r0; try reflexivity.
  cbn.
  rewrite IHr0_2,Str_app_assoc.
  reflexivity.
Qed.

Definition repeat_S_def(r0:seg_expr):=
  let n:=nat_var 1%positive in
  let r:=side_var 2%positive in
  (side_eq
  (side_concat (seg_repeat r0 (nat_add n (from_nat 1))) r)
  (side_concat_unfold r0 (side_concat (seg_repeat r0 n) r)),
  3%positive).

Lemma repeat_S_def_spec r0:
  to_prop0' (fst (repeat_S_def r0)).
Proof.
  unfold to_prop0'.
  intros.
  cbn.
  rewrite N.add_comm.
  rewrite Nnat.N2Nat.inj_add.
  rewrite lpow_add.
  rewrite Str_app_assoc.
  change (N.to_nat 1) with 1.
  cbn.
  rewrite List.app_nil_r.
  rewrite side_concat_unfold_spec.
  reflexivity.
Qed.

Definition repeat_2_def(r0:seg_expr):=
  let r:=side_var 1%positive in
  (side_eq
  (side_concat (seg_repeat r0 (from_nat 2)) r)
  (side_concat_unfold r0 (side_concat_unfold r0 r)),
  2%positive).

Lemma repeat_2_def_spec r0:
  to_prop0' (fst (repeat_2_def r0)).
Proof.
  unfold to_prop0'.
  intros.
  cbn.
  change (Pos.to_nat 2) with 2.
  cbn.
  repeat rewrite Str_app_assoc.
  cbn.
  do 2 rewrite side_concat_unfold_spec.
  reflexivity.
Qed.

Definition repeat_0_def(r0:seg_expr):=
  let r:=side_var 1%positive in
  (side_eq
  (side_concat (seg_repeat r0 (from_nat 0)) r)
  r,
  2%positive).

Lemma repeat_0_def_spec r0:
  to_prop0' (fst (repeat_0_def r0)).
Proof.
  unfold to_prop0'.
  reflexivity.
Qed.

Definition repeat_0_def'(r0:seg_expr):=
  let r:=side_var 1%positive in
  (side_eq
  r
  (side_concat (seg_repeat r0 (from_nat 0)) r),
  2%positive).

Lemma repeat_0_def_spec' r0:
  to_prop0' (fst (repeat_0_def' r0)).
Proof.
  unfold to_prop0'.
  reflexivity.
Qed.

Definition step1 m s sgn :=
  let l:=side_var 1%positive in
  let r:=side_var 2%positive in
  match tm (s,m) with
  | None => None
  | Some (m',sgn',s') =>
    Some (
    if dir_eqb sgn sgn' then
      (multistep'_expr
      (l,side_concat (seg_sym m) r,s,sgn)
      (side_concat (seg_sym m') l,r,s',sgn)
      true,
      3%positive)
    else
      (multistep'_expr
      (l,side_concat (seg_sym m) r,s,sgn)
      (side_concat (seg_sym m') r,l,s',sgn')
      true,
      3%positive))
  end.

Lemma step1_spec m s sgn:
  match step1 m s sgn with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  unfold step1.
  destruct (tm (s,m)) as [[[m' sgn'] s']|] eqn:E.
  2: trivial.
  destruct sgn,sgn'; unfold to_prop0'; intros; cbn.
  all: apply progress_base; constructor; apply E.
Qed.

Fixpoint side_find_repeat_2_fold(ls1 ls2:side_expr)(n:nat):=
match n with
| O =>
  match ls1,ls2 with
  | side_concat h1 t1,side_concat h2 t2 =>
    if seg_expr_eqb h1 h2 then Some h1 else None
  | _,_ => None
  end
| Datatypes.S n0 =>
  match ls1,ls2 with
  | side_concat h1 t1,side_concat h2 t2 =>
    if seg_expr_eqb h1 h2 then
      match side_find_repeat_2_fold t1 t2 n0 with
      | Some v => Some (seg_concat h1 v)
      | None => None
      end
    else None
  | _,_ => None
  end
end.

Fixpoint side_check_repeat_S_fold(ls1:side_expr)(ls2:seg_expr)(n:nat):=
match n with
| O =>
  match ls1 with
  | side_concat h1 t1 => seg_expr_eqb h1 ls2
  | _ => false
  end
| Datatypes.S n0 =>
  match ls1,ls2 with
  | side_concat h1 t1,seg_concat h2 t2 =>
     seg_expr_eqb h1 h2 && side_check_repeat_S_fold t1 t2 n0
  | _,_ => false
  end
end.

Definition side_find_repeat_S_fold ls1 ls2 n :=
match ls2 with
| side_concat (seg_repeat h2 _) _ =>
  if side_check_repeat_S_fold ls1 h2 n then Some h2 else None
| _ => None
end.

Definition side_find_repeat_O_fold ls :=
match ls with
| side_concat (seg_repeat h (from_nat 0)) _ => Some h
| _ => None
end.

Definition side_find_repeat_fold_1 ls1 ls2 n :=
match side_find_repeat_2_fold ls1 ls2 n with
| Some h => Some (repeat_2_def h)
| None =>
  match side_find_repeat_S_fold ls1 ls2 n with
  | Some h => Some (repeat_S_def h)
  | None => None
  end
end.

Fixpoint side_find_repeat_fold_2 ls1 ls2 n n0 {struct n0} :=
match n0 with
| O => None
| Datatypes.S n1 =>
  match
    match n with
    | Datatypes.S n2 => side_find_repeat_fold_1 ls1 ls2 n2
    | O => None
    end
  with
  | Some h => Some h
  | None =>
    match ls2 with
    | side_concat h2 t2 =>
      side_find_repeat_fold_2 ls1 t2 (Datatypes.S n) n1
    | _ => None
    end
  end
end.

Definition side_concat_rw_2(x:prop0_expr*id_t):prop0_expr*id_t :=
match x with
| (side_eq a b,p) =>
  let (v,p):=(seg_var p,Pos.succ p) in
  (side_eq (side_concat v a) (side_concat v b),p)
| _ => x
end.

Lemma side_concat_rw_2_spec x:
  to_prop0' (fst x) ->
  to_prop0' (fst (side_concat_rw_2 x)).
Proof.
  unfold to_prop0'.
  destruct x as [x i].
  cbn.
  intros H mp mpi.
  specialize (H mp mpi).
  destruct x; cbn; cbn in H; congruence.
Qed.

Definition max_repeater_len:nat := 8.

Fixpoint side_find_repeat_fold ls1 :=
match side_find_repeat_O_fold ls1 with
| Some h => Some (repeat_0_def' h)
| None =>
  match ls1 with
  | side_concat h1 t1 =>
    match side_find_repeat_fold t1 with
    | Some v => Some (side_concat_rw_2 v)
    | None =>
      match side_find_repeat_fold_2 ls1 ls1 O max_repeater_len with
      | Some v => Some v
      | None => None
      end
    end
  | _ => None
  end
end.

Opaque max_repeater_len.

Lemma side_find_repeat_fold_1_spec ls1 ls2 n:
  match side_find_repeat_fold_1 ls1 ls2 n with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  unfold side_find_repeat_fold_1.
  destruct (side_find_repeat_2_fold ls1 ls2 n).
  1: apply repeat_2_def_spec.
  destruct (side_find_repeat_S_fold ls1 ls2 n).
  1: apply repeat_S_def_spec.
  trivial.
Qed.


Lemma side_find_repeat_fold_2_spec ls1 ls2 n n0:
  match side_find_repeat_fold_2 ls1 ls2 n n0 with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  gen ls2 n.
  induction n0; cbn; intros; trivial.
  destruct n as [|n]; cbn.
  - destruct ls2; cbn; trivial.
    apply IHn0.
  - pose proof (side_find_repeat_fold_1_spec ls1 ls2 n) as H.
    destruct (side_find_repeat_fold_1 ls1 ls2 n); try tauto.
    destruct ls2; cbn; trivial.
    apply IHn0.
Qed.

Lemma side_find_repeat_fold_spec ls:
  match side_find_repeat_fold ls with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  induction ls.
  1,2: cbn; trivial.
  cbn[side_find_repeat_fold].
  destruct (side_find_repeat_O_fold (side_concat a ls)).
  1: apply repeat_0_def_spec'.
  destruct (side_find_repeat_fold ls).
  - apply side_concat_rw_2_spec,IHls.
  - pose proof (side_find_repeat_fold_2_spec (side_concat a ls) (side_concat a ls) 0 max_repeater_len).
    destruct (side_find_repeat_fold_2 (side_concat a ls) (side_concat a ls) 0 max_repeater_len); tauto.
Qed.

Transparent max_repeater_len.

Definition config_rw_l(x:prop0_expr*id_t) s sgn:prop0_expr*id_t :=
match x with
| (side_eq l1 l2,p) =>
  let (r,p):=(side_var p,Pos.succ p) in 
  (config_eq (l1,r,s,sgn) (l2,r,s,sgn),p)
| _ => x
end.

Definition config_rw_r(x:prop0_expr*id_t) s sgn:prop0_expr*id_t :=
match x with
| (side_eq r1 r2,p) =>
  let (l,p):=(side_var p,Pos.succ p) in 
  (config_eq (l,r1,s,sgn) (l,r2,s,sgn),p)
| _ => x
end.

Lemma config_rw_l_spec x s sgn:
  to_prop0' (fst x) ->
  to_prop0' (fst (config_rw_l x s sgn)).
Proof.
  unfold to_prop0'.
  destruct x as [x i]; cbn.
  intros H mp.
  specialize (H mp).
  destruct x,sgn; cbn; cbn in H; try tauto; congruence.
Qed.

Lemma config_rw_r_spec x s sgn:
  to_prop0' (fst x) ->
  to_prop0' (fst (config_rw_r x s sgn)).
Proof.
  unfold to_prop0'.
  destruct x as [x i]; cbn.
  intros H mp.
  specialize (H mp).
  destruct x,sgn; cbn; cbn in H; try tauto; congruence.
Qed.

Definition config_find_repeat_fold(c:config_expr) :=
let '(l,r,s,sgn):=c in
match side_find_repeat_fold l with
| Some x => Some (config_rw_l x s sgn)
| None =>
  match side_find_repeat_fold r with
  | Some x => Some (config_rw_r x s sgn)
  | None => None
  end
end.

Lemma config_find_repeat_fold_spec c:
  match config_find_repeat_fold c with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  destruct c as [[[l r] s] sgn]; cbn.
  pose proof (side_find_repeat_fold_spec l) as H.
  destruct (side_find_repeat_fold l).
  1: apply config_rw_l_spec,H.
  pose proof (side_find_repeat_fold_spec r) as H0.
  destruct (side_find_repeat_fold r).
  1: apply config_rw_r_spec,H0.
  trivial.
Qed.



Definition side_find_repeat_unfold ls :=
match ls with
| side_0inf => Some side_0inf_def
| side_concat (seg_repeat a (from_nat 0)) r => Some (repeat_0_def a)
| side_concat (seg_repeat a _) r => Some (repeat_S_def a)
| _ => None
end.

Lemma side_find_repeat_unfold_spec ls:
  match side_find_repeat_unfold ls with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  destruct ls; cbn; trivial.
  - apply side_0inf_def_spec.
  - destruct a; trivial.
    destruct n.
    1: destruct n.
    all: try (apply repeat_S_def_spec).
    apply repeat_0_def_spec.
Qed.

Definition config_find_repeat_unfold(c:config_expr) :=
let '(l,r,s,sgn):=c in
  match side_find_repeat_unfold r with
  | Some x => Some (config_rw_r x s sgn)
  | None => None
  end.

Lemma config_find_repeat_unfold_spec c:
  match config_find_repeat_unfold c with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  destruct c as [[[l r] s] sgn].
  cbn.
  pose proof (side_find_repeat_unfold_spec r) as H.
  destruct (side_find_repeat_unfold r); trivial.
  apply config_rw_r_spec,H.
Qed.

Definition step0_rw_l(x:prop0_expr*id_t) :=
match x with
| (config_eq c1 c2,p) =>
  (multistep'_expr c2 c1 false,p)
| _ => x
end.

Definition step0_rw_r(x:prop0_expr*id_t) :=
match x with
| (config_eq c1 c2,p) =>
  (multistep'_expr c1 c2 false,p)
| _ => x
end.

Lemma step0_rw_l_spec x:
  to_prop0' (fst x) ->
  to_prop0' (fst (step0_rw_l x)).
Proof.
  unfold to_prop0'.
  destruct x as [x i].
  cbn.
  intros H mp mpi.
  specialize (H mp mpi).
  destruct x; cbn; cbn in H; try tauto.
  rewrite H.
  constructor.
Qed.

Lemma step0_rw_r_spec x:
  to_prop0' (fst x) ->
  to_prop0' (fst (step0_rw_r x)).
Proof.
  unfold to_prop0'.
  destruct x as [x i].
  cbn.
  intros H mp mpi.
  specialize (H mp mpi).
  destruct x; cbn; cbn in H; try tauto.
  rewrite H.
  constructor.
Qed.



Definition prop0_to_prop(x:prop0_expr*id_t):prop_expr' :=
let (x,i):=x in
(([],[x]),i).

Definition next_rule f x :=
match get_config_r x with
| None => None
| Some c =>
  match f c with
  | None => None
  | Some x0 => Some (prop0_to_prop x0)
  end
end.

Lemma prop0_to_prop_spec x:
  to_prop0' (fst x) ->
  to_prop' (fst (prop0_to_prop x)).
Proof.
  destruct x as [x i]; cbn.
  intros H mpi mp.
  specialize (H mp mpi).
  cbn.
  unfold to_prop0_list.
  repeat rewrite Forall_cons_iff.
  repeat rewrite Forall_nil_iff.
  tauto.
Qed.

Lemma next_rule_spec f x:
  (forall c,
  match f c with
  | None => True
  | Some x => to_prop0' (fst x)
  end) ->
  to_prop' (fst x) ->
  match next_rule f x with
  | None => True
  | Some x0 => to_prop' (fst x0)
  end.
Proof.
  intros H0 H.
  unfold next_rule.
  destruct (get_config_r x); trivial.
  specialize (H0 c).
  destruct (f c); trivial.
  apply prop0_to_prop_spec,H0.
Qed.

Definition hlin_layer:Type := (prop_expr'*prop_expr')*(prop_expr'*prop_expr')*(N*N).

Definition hlin_layer_WF(x:hlin_layer):Prop :=
  let '((w1_,w0_),(w1,w0),_):=x in
  to_prop' (fst w1_) /\
  to_prop' (fst w0_) /\
  to_prop' (fst w1) /\
  to_prop' (fst w0).

Definition hlin_layers_WF(x:list hlin_layer):Prop :=
  Forall hlin_layer_WF x.

Definition step0_refl' x :=
match find_step0_refl x with
| None => x
| Some x => x
end.

Lemma step0_refl'_spec x:
  to_prop' (fst x) ->
  to_prop' (fst (step0_refl' x)).
Proof.
  unfold step0_refl'.
  pose proof (find_step0_refl_spec x).
  destruct (find_step0_refl x); tauto.
Qed.

Definition reset_hlin_layers u0 :=
((step0_refl' u0,u0),(step0_refl' u0,u0),(1,2)%N)::nil.

Lemma reset_hlin_layers_spec x:
  to_prop' (fst x) ->
  hlin_layers_WF (reset_hlin_layers x).
Proof.
  intro H.
  unfold hlin_layers_WF,reset_hlin_layers.
  apply Forall_cons; auto.
  cbn.
  repeat split; auto using step0_refl'_spec.
Qed.

Definition get_w0(ls:list hlin_layer)(u:prop_expr') :=
match ls with
| (_,(_,w0),_)::ls => w0
| _ => u
end.

Lemma get_w0_spec ls u :
  hlin_layers_WF ls ->
  to_prop' (fst u) ->
  to_prop' (fst (get_w0 ls u)).
Proof.
  destruct ls; cbn.
  1: tauto.
  destruct h as [[[w1_ w0_] [w1 w0]] [l r]]; cbn.
  unfold hlin_layers_WF.
  rewrite Forall_cons_iff; cbn.
  tauto.
Qed.

(*
  u1: Q2 --> Q3
  u0: c0 --> P := w0 u1

  w1_: Q0 --> Q1
  w1: Q1 --> Q2
  w0 := w0_ w1
*)
Fixpoint hlin_layers_upd(u1 u0:prop_expr')(ls:list hlin_layer): (list hlin_layer) :=
let u := (reset_hlin_layers u0) in
match ls with
| nil => u
| w::ls =>
  let '((w1_,w0_),(w1,_),(l,r)) := w in
  match follow_rule w1 u1 with
  | None => u
  | Some w1' =>
    match try_ind w1' w0_ u0 with
    | Some (u1',u0') =>
      match follow_rule w1_ u1' with
      | None => reset_hlin_layers u1'
      | Some w1'' =>
        let ls':=hlin_layers_upd w1'' u0' ls in
        let u0'':= get_w0 ls' u0' in
        ((step0_refl' u0'',u0''),(step0_refl' u0'',u0''),(1,2)%N)::
        ls'
      end
    | None =>
      let l := N.succ l in
      if (l<?r)%N then
        ((w1_,w0_),(w1',u0),(l,r))::ls
      else
        match follow_rule w1_ w1' with
        | None => u
        | Some w1_ =>
          ((w1_,u0),(step0_refl' u0,u0),(l,r*2)%N)::ls
        end
    end
  end
end.

Lemma hlin_layers_upd_spec u1 u0 ls:
  to_prop' (fst u1) ->
  to_prop' (fst u0) ->
  hlin_layers_WF ls ->
  hlin_layers_WF (hlin_layers_upd u1 u0 ls).
Proof.
  gen u1 u0.
  induction ls; introv H1 H0 H.
  1: apply reset_hlin_layers_spec,H0.
  unfold hlin_layers_WF in H.
  rewrite Forall_cons_iff in H.
  destruct H as [Ha Hls].
  destruct a as [[[w1_ w0_] [w1 w0]] [l r]].
  cbn in Ha.
  cbn.
  pose proof (follow_rule_spec' w1 u1).
  destruct (follow_rule w1 u1) as [w1'|].
  2: apply reset_hlin_layers_spec; tauto.
  pose proof (try_ind_spec w1' w0_ u0).
  destruct (try_ind w1' w0_ u0) as [[u1' u0']|].
  - pose proof (follow_rule_spec' w1_ u1').
    destruct (follow_rule w1_ u1').
    2: apply reset_hlin_layers_spec; try tauto.
    unfold hlin_layers_WF.
    apply Forall_cons.
    2: apply IHls; tauto.
    cbn.
    epose proof (get_w0_spec (hlin_layers_upd p u0' ls) u0' _ _).
    pose proof (step0_refl'_spec (get_w0 (hlin_layers_upd p u0' ls) u0')).
    repeat split; tauto.
    Unshelve.
      2: tauto.
      apply IHls; tauto.
  - destruct (N.succ l <? r)%N.
    + unfold hlin_layers_WF.
      apply Forall_cons; try tauto.
      cbn.
      repeat split; tauto.
    + pose proof (follow_rule_spec' w1_ w1').
      destruct (follow_rule w1_ w1').
      2: apply reset_hlin_layers_spec; tauto.
      unfold hlin_layers_WF.
      apply Forall_cons; try tauto.
      cbn.
      pose proof (step0_refl'_spec u0).
      repeat split; tauto.
Qed.


Definition find_repeat_unfold x :=
match get_config_r x with
| None => None
| Some x =>
  match config_find_repeat_unfold x with
  | None => None
  | Some x =>
    Some (prop0_to_prop (step0_rw_r x))
  end
end.

Definition find_repeat_fold x :=
match get_config_r x with
| None => None
| Some x =>
  match config_find_repeat_fold x with
  | None => None
  | Some x =>
    Some (prop0_to_prop (step0_rw_l x))
  end
end.

Definition find_step1 x :=
match get_config_r x with
| None => None
| Some x =>
  let '(l,r,s,sgn):=x in
  match r with
  | side_concat (seg_sym m) r0 =>
    match step1 m s sgn with
    | None => None
    | Some x0 => Some (prop0_to_prop x0)
    end
  | _ => None 
  end
end.

Lemma find_repeat_unfold_spec x:
to_prop' (fst x) ->
match find_repeat_unfold x with
| None => True
| Some x =>
  to_prop' (fst x)
end.
Proof.
  intros H.
  unfold find_repeat_unfold.
  destruct (get_config_r x); trivial.
  destruct_spec config_find_repeat_unfold_spec; trivial.
  apply prop0_to_prop_spec.
  apply step0_rw_r_spec,H0.
Qed.

Lemma find_repeat_fold_spec x:
to_prop' (fst x) ->
match find_repeat_fold x with
| None => True
| Some x =>
  to_prop' (fst x)
end.
Proof.
  intros H.
  unfold find_repeat_fold.
  destruct (get_config_r x); trivial.
  destruct_spec config_find_repeat_fold_spec; trivial.
  apply prop0_to_prop_spec.
  apply step0_rw_l_spec,H0.
Qed.

Lemma find_step1_spec x:
to_prop' (fst x) ->
match find_step1 x with
| None => True
| Some x =>
  to_prop' (fst x)
end.
Proof.
  intros H.
  unfold find_step1.
  destruct (get_config_r x) as [[[[l r] s] sgn]|]; trivial.
  destruct r; trivial.
  destruct a; trivial.
  destruct_spec step1_spec; trivial.
  apply prop0_to_prop_spec,H0.
Qed.


Definition hlin_layers_upd' (ls:list hlin_layer)(f:prop_expr'->option prop_expr') :=
match ls with
| (_,(w1,w0),_)::_ =>
  if (snd w0 =? 1)%positive then
    match f w0 with
    | None => None
    | Some u1 =>
      match follow_rule w0 u1 with
      | None => None
      | Some u0 =>
        Some (hlin_layers_upd u1 u0 ls)
      end
    end
  else None
| _ => None
end.

Lemma hlin_layers_upd'_spec ls f:
hlin_layers_WF ls ->
(forall x,
to_prop' (fst x) ->
match f x with
| None => True
| Some x =>
  to_prop' (fst x)
end) ->
match hlin_layers_upd' ls f with
| None => True
| Some ls' => hlin_layers_WF ls'
end.
Proof.
  intros Hls Hf.
  unfold hlin_layers_upd'.
  destruct ls as [|[[[w1_ w0_] [w1 w0]] [l r]] ls0]; trivial.
  destruct (snd w0 =? 1)%positive; trivial.
  specialize (Hf w0).
  pose proof Hls as Hls'.
  unfold hlin_layers_WF in Hls.
  rewrite Forall_cons_iff in Hls.
  cbn in Hls.
  destruct (f w0); trivial.
  destruct_spec follow_rule_spec'; trivial.
  apply hlin_layers_upd_spec; tauto.
Qed.

Fixpoint Pos_iter_until{S S'}(f:S->S+S')(x:S+S')(T:positive):S+S' :=
match x with
| inl s =>
  match T with
  | xH => f s
  | xO T0 => Pos_iter_until f (Pos_iter_until f x T0) T0
  | xI T0 => Pos_iter_until f (Pos_iter_until f (f s) T0) T0
  end
| _ => x
end.

Definition N_iter_until{S S'}(f:S->S+S')(x:S+S')(T:N):S+S' :=
match T with
| N0 => x
| Npos T0 => Pos_iter_until f x T0
end.


Definition hlin_layers_step(s:(list hlin_layer)*bool):(list hlin_layer)*bool+(list hlin_layer) :=
let (ls,o):=s in
if o then
  match hlin_layers_upd' ls find_step1 with
  | None =>
    match hlin_layers_upd' ls find_repeat_unfold with
    | None => inr ls
    | Some ls => inl (ls,true)
    end
  | Some ls =>
    inl (ls,false)
  end
else
  match hlin_layers_upd' ls find_repeat_fold with
  | None => inl (ls,true)
  | Some ls => inl (ls,false)
  end.

Definition step0_refl_c0:prop_expr' :=
  ([],[multistep'_expr (side_0inf,side_0inf,q0,R) (side_0inf,side_0inf,q0,R) false],1%positive).

Lemma step0_refl_c0_spec:
  to_prop' (fst step0_refl_c0).
Proof.
  intros mpi mp.
  cbn.
  unfold to_prop0_list; cbn.
  repeat rewrite Forall_cons_iff.
  repeat rewrite Forall_nil_iff.
  cbn.
  intro; split; trivial.
Qed.

Definition hlin_layers_steps T :=
N_iter_until hlin_layers_step (inl (reset_hlin_layers step0_refl_c0,true)) T.

End tm_ctx.

Declare Scope ind_scope.
Delimit Scope ind_scope with ind.
Bind Scope ind_scope with nat_expr.
Bind Scope ind_scope with seg_expr.
Bind Scope ind_scope with side_expr.
Bind Scope ind_scope with config_expr.

Notation "a *> b" := (side_concat a b) : ind_scope.
Notation "a ; b" := (seg_concat a b) (at level 60, right associativity): ind_scope.
Notation "a ^ b" := (seg_repeat a b) : ind_scope.
Coercion seg_sym: Sym>->seg_expr.
Notation "a + b" := (nat_add a b) : ind_scope.
Notation "a * b" := (nat_mul a b) : ind_scope.
Coercion from_nat: N>->nat_expr.
Notation "'nv' a" := (nat_var a) (at level 35).
Notation "'segv' a" := (seg_var a) (at level 35).
Notation "'sv' a" := (side_var a) (at level 35).
Notation "a -->* b" := (multistep'_expr a b false) (at level 40).
Notation "a -->+ b" := (multistep'_expr a b true) (at level 40).
Notation "'0...'" := side_0inf.


(*
config_find_repeat_unfold, step0_rw_r
step1
config_find_repeat_fold, step0_rw_l
*)

(*
  (i i) (i i i)*
  i+1 () ()
*)




(*
(forall x, P(x,0)-->Q(x,0)) ->

(forall n, (forall x, P(x,n)-->Q(x,n)) -> (forall x, P(x,n+1)-->Q(x,n+1))) ->

(forall n, forall x, P(x,n)-->Q(x,n))
*)




(*
prop_solve_eq: ((a,b)=(c,d) -> P) -> (a=c -> b=d -> P), also simpl nat affine map in H
try_subst: (forall a, P(a)) -> forall a, P(f(a))
prop_has_false: (False -> P) is trivial
prop_eqb: check progress
prop_merge: (A->B) -> (C->D) -> (A->C->(B/\D))
simpl_prop: simpl nat affine map
prop_multistep'_trans: (A-->B) -> (C-->D) -> (B=C -> A-->D)

follow_rule: (A-->B) -> (B-->C) -> (A-->C)

TODO WIP: induction
TODO WIP: basic lemmas for TM execute and simpl tape
*)

End Inductive.





