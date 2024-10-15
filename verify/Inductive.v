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

Definition multistep_lb tm (n:nat) s0 s1 :=
exists n0, n<=n0 /\ s0 -[tm]->> n0 / s1.

Lemma multistep_lb_multistep tm n s0 s1:
  multistep_lb tm n s0 s1 ->
  exists s2, multistep tm n s0 s2.
Proof.
  gen s0 s1.
  induction n; intros s0 s1 H.
  - exists s0.
    constructor.
  - destruct H as [n0 [H0 H1]].
    destruct n0 as [|n0]. 1: lia.
    inverts H1.
    epose proof (IHn c' s1 _) as H4.
    destruct H4 as [s2 H4].
    eexists.
    econstructor; eauto.
Unshelve.
  eexists.
  split. 2: eauto. lia.
Qed.

Lemma multistep_lb_nonhalt tm:
  (forall n, exists s, multistep_lb tm n c0 s) ->
  ~halts tm c0.
Proof.
  intro H.
  intros [n H0].
  destruct (H (S n)) as [s H1].
  destruct (multistep_lb_multistep _ _ _ _ H1) as [s' H2].
  eapply exceeds_halt; eauto.
Qed.



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
| seg_nil
| seg_sym(a:Sym)
| seg_concat(a:seg_expr)(b:seg_expr)
| seg_repeat(a:seg_expr)(n:nat_expr)
| seg_arithseq(a:list ((list Sym)*Z*nat_expr))(n:nat_expr)
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
| multistep_lb_expr(a b:config_expr)(n:nat_expr)
| multistep'_expr(a b:config_expr)(n:bool)
.

Definition prop_expr:Type :=
  (list prop0_expr)*(list prop0_expr).


Ltac solve_Bool_reflect :=
  try (constructor; congruence).

Fixpoint list_eqb{T}(T_eqb:T->T->bool)(a b:list T):bool :=
match a,b with
| a0::a1,b0::b1 => (T_eqb a0 b0) && (list_eqb T_eqb a1 b1)
| nil,nil => true
| _,_ => false
end.

Lemma list_eqb_spec {T} T_eqb (a b:list T):
  (forall a0 b0, Bool.reflect (a0=b0) (T_eqb a0 b0)) ->
  Bool.reflect (a=b) (list_eqb T_eqb a b).
Proof.
  intro H.
  gen b.
  induction a as [|a0 a1]; intros b; destruct b as [|b0 b1]; cbn.
  all: solve_Bool_reflect.
  destruct (H a0 b0),(IHa1 b1); solve_Bool_reflect.
Qed.

Definition prod_eqb{A B}(A_eqb:A->A->bool)(B_eqb:B->B->bool)(a b:A*B):bool :=
match a,b with
| (a0,a1),(b0,b1) =>
  A_eqb a0 b0 && B_eqb a1 b1
end.

Lemma prod_eqb_spec{A B} A_eqb B_eqb (a b:A*B):
  (forall a0 b0, Bool.reflect (a0=b0) (A_eqb a0 b0)) ->
  (forall a0 b0, Bool.reflect (a0=b0) (B_eqb a0 b0)) ->
  Bool.reflect (a=b) (prod_eqb A_eqb B_eqb a b).
Proof.
  intros Ha Hb.
  destruct a as [a0 a1].
  destruct b as [b0 b1]; cbn.
  destruct (Ha a0 b0),(Hb a1 b1); solve_Bool_reflect.
Qed.

Fixpoint nat_expr_eqb(a b:nat_expr):bool :=
match a,b with
| from_nat a0,from_nat b0 => (a0 =? b0)%N
| nat_add a0 a1,nat_add b0 b1 => (nat_expr_eqb a0 b0) && (nat_expr_eqb a1 b1)
| nat_mul a0 a1,nat_mul b0 b1 => (nat_expr_eqb a0 b0) && (nat_expr_eqb a1 b1)
| nat_var a0,nat_var b0 => (a0 =? b0)%positive
| nat_ivar,nat_ivar => true
| _,_ => false
end.

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
| seg_nil,seg_nil => true
| seg_sym a0,seg_sym b0 => sym_eqb a0 b0
| seg_concat a0 a1,seg_concat b0 b1 => seg_expr_eqb a0 b0 && seg_expr_eqb a1 b1
| seg_repeat a0 an,seg_repeat b0 bn => seg_expr_eqb a0 b0 && nat_expr_eqb an bn
| seg_arithseq a0 an,seg_arithseq b0 bn =>
  nat_expr_eqb an bn &&
  list_eqb (prod_eqb (prod_eqb (list_eqb sym_eqb) Z.eqb) nat_expr_eqb) a0 b0
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
  - destruct (nat_expr_eqb_spec n n0); solve_Bool_reflect.
    destruct (list_eqb_spec (prod_eqb (prod_eqb (list_eqb sym_eqb) Z.eqb) nat_expr_eqb) a a0);
    solve_Bool_reflect.
    intros.
    apply prod_eqb_spec; intros.
    1: apply prod_eqb_spec; intros.
    1: apply list_eqb_spec,sym_eqb_spec.
    1: apply Z.eqb_spec.
    1: apply nat_expr_eqb_spec.
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
| multistep_lb_expr a0 a1 an,multistep_lb_expr b0 b1 bn =>
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

Fixpoint solve_arithseq_eq(a b:list ((list Sym) * Z * nat_expr)):list prop0_expr :=
match a,b with
| nil,nil => []
| (a0,a1,a2)::a3,(b0,b1,b2)::b3 =>
  if list_eqb sym_eqb a0 b0 && Z.eqb a1 b1 then
    (solve_nat_eq a2 b2) ++ (solve_arithseq_eq a3 b3)
  else [false_prop0]
| _,_ => [false_prop0]
end.

Fixpoint solve_seg_eq(a b:seg_expr):list prop0_expr :=
match a,b with
| seg_nil,seg_nil => []
| seg_sym a0,seg_sym b0 => if sym_eqb a0 b0 then [] else [false_prop0]
| seg_concat a0 a1,seg_concat b0 b1 => (solve_seg_eq a0 b0) ++ (solve_seg_eq a1 b1)
| seg_repeat a0 a1,seg_repeat b0 b1 => (solve_seg_eq a0 b0) ++ (solve_nat_eq a1 b1)
| seg_arithseq a0 a1,seg_arithseq b0 b1 => (solve_arithseq_eq a0 b0) ++ (solve_nat_eq a1 b1)
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
| seg_nil,seg_nil => true
| seg_sym a0,seg_sym b0 => sym_eqb a0 b0
| seg_concat a0 a1,seg_concat b0 b1 => seg_expr_eqb a0 b0 && seg_expr_eqb a1 b1
| seg_repeat a0 an,seg_repeat b0 bn => seg_expr_eqb a0 b0 && nat_expr_eqb an bn
| seg_arithseq a0 an,seg_arithseq b0 bn =>
  nat_expr_eqb an bn &&
  list_eqb (prod_eqb (prod_eqb (list_eqb sym_eqb) Z.eqb) nat_expr_eqb) a0 b0
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
| multistep_lb_expr a0 a1 an,multistep_lb_expr b0 b1 bn =>
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

Definition seg_arithseq_allFV(x:list ((list Sym)*Z*nat_expr)):S->S :=
List.fold_left (fun s x => let '(_,_,x2):=x in (nat_allFV x2 s)) x.

Fixpoint seg_allFV(x:seg_expr)(s:S):S :=
match x with
| seg_nil => s
| seg_sym a => s
| seg_concat a b => seg_allFV a (seg_allFV b s)
| seg_repeat a n => seg_allFV a (nat_allFV n s)
| seg_arithseq a n => seg_arithseq_allFV a (nat_allFV n s)
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
| multistep_lb_expr a b n => config_allFV a (config_allFV b (nat_allFV n s))
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
| seg_nil => x
| seg_sym a => x
| seg_concat a b => seg_concat (simpl_seg a) (simpl_seg b)
| seg_repeat a n => seg_repeat (simpl_seg a) (simpl_nat n)
| seg_arithseq a n => seg_arithseq (map (fun '(x0,x1,x2) => (x0,x1, simpl_nat x2)) a) (simpl_nat n)
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
| multistep_lb_expr x0 x1 n => multistep_lb_expr (simpl_config x0) (simpl_config x1) (simpl_nat n)
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
| seg_nil => x
| seg_sym a => x
| seg_concat a b => seg_concat (subst_seg a) (subst_seg b)
| seg_repeat a n => seg_repeat (subst_seg a) (subst_nat n)
| seg_arithseq a n => seg_arithseq (map (fun '(x0,x1,x2) => (x0,x1,subst_nat x2)) a) (subst_nat n)
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
| multistep_lb_expr x0 x1 n => multistep_lb_expr (subst_config x0) (subst_config x1) (subst_nat n)
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



Definition solve_assumptions_iter_limit:nat := 1024.

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
| (H,[multistep_lb_expr s1 s2 n1;multistep_lb_expr s3 s4 n2]) => Some ((config_eq s2 s3)::H,[multistep_lb_expr s1 s4 (nat_add n1 n2)])
| _ => None
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

Definition visit_nat(an bn ca cb:nat_expr): option (nat_expr*nat_expr*(list prop0_expr)) :=
match ca,cb with
| from_nat can,from_nat cbn =>
  if (can <=? cbn)%N then (* inc *)
    let d := (cbn-can)%N in
    let an' := (nat_add an (nat_mul (nat_ivar) (from_nat d))) in
    Some (an,an',[nat_eq (nat_add an (from_nat d)) bn]) (* inc *)
  else (* dec *)
    let d := (can-cbn)%N in
    let bn' := (nat_add bn (nat_mul (nat_ivar) (from_nat d))) in
    Some (bn',bn,[nat_eq (nat_add bn (from_nat d)) an]) (* dec *)
| _,_ => None
end.

Fixpoint visit_seg_arithseq(a b ca cb:list ((list Sym)*Z*nat_expr)):=
match a,b,ca,cb with
| (a0,a1,a2)::a,(b0,b1,b2)::b,(ca0,ca1,ca2)::ca,(cb0,cb1,cb2)::cb =>
  if list_eqb sym_eqb a0 b0 && list_eqb sym_eqb a0 ca0 && list_eqb sym_eqb a0 cb0 &&
    Z.eqb a1 b1 && Z.eqb a1 ca1 && Z.eqb a1 cb1
  then
    match visit_nat a2 b2 ca2 cb2,visit_seg_arithseq a b ca cb with
    | Some (n2,n2',ls2),Some (ls,ls',ls3) =>
      Some ((a0,a1,n2)::ls,(a0,a1,n2')::ls',ls2++ls3)
    | _,_ => None
    end
  else None
| [],[],[],[] => Some ([],[],[])
| _,_,_,_ => None
end.

Definition visit_seg(a b ca cb:seg_expr):option (seg_expr*seg_expr*(list prop0_expr)) :=
if seg_expr_eqb a b then Some (a,a,[]) else
match a,b,ca,cb with
| seg_repeat a0 an,seg_repeat b0 bn,seg_repeat ca0 can,seg_repeat cb0 cbn =>
  if seg_expr_eqb a0 b0 && seg_expr_eqb a0 ca0 && seg_expr_eqb a0 cb0 then
    match visit_nat an bn can cbn with
    | Some (n1,n2,ls) => Some (seg_repeat a0 n1,seg_repeat a0 n2,ls)
    | None => None
    end
  else None
| seg_arithseq a0 an,seg_arithseq b0 bn,seg_arithseq ca0 can,seg_arithseq cb0 cbn =>
  match visit_nat an bn can cbn,visit_seg_arithseq a0 b0 ca0 cb0 with
  | Some (n1,n2,ls),Some (ls1,ls2,ls3) =>
    Some (seg_arithseq ls1 n1,seg_arithseq ls2 n2,ls++ls3)
  | _,_ => None
  end
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

Definition visit_config'(c:config_expr)(p:id_t) :=
let '(l3,r3,s3,sgn3):=c in
let (lx,p):=(side_var p,Pos.succ p) in
let (rx,p):=(side_var p,Pos.succ p) in
((lx,rx,s3,sgn3),p).

End visit.
End Visit2.

Module Visit3.
(* guess n *)

Definition visit_nat(an bn ca cb:nat_expr):option N :=
match ca,cb with
| from_nat can,from_nat cbn =>
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
| _,_ => None
end.

Fixpoint visit_seg_arithseq(a b ca cb:list ((list Sym)*Z*nat_expr)):option N:=
match a,b,ca,cb with
| (a0,a1,a2)::a,(b0,b1,b2)::b,(ca0,ca1,ca2)::ca,(cb0,cb1,cb2)::cb =>
  oNmin
  (visit_nat a2 b2 ca2 cb2)
  (visit_seg_arithseq a b ca cb)
| _,_,_,_ => None
end.

Definition visit_seg(a b ca cb:seg_expr):option N :=
match a,b,ca,cb with
| seg_repeat a0 an,seg_repeat b0 bn,seg_repeat ca0 can,seg_repeat cb0 cbn =>
  visit_nat an bn can cbn
| seg_arithseq a0 an,seg_arithseq b0 bn,seg_arithseq ca0 can,seg_arithseq cb0 cbn =>
  oNmin
  (visit_seg_arithseq a0 b0 ca0 cb0)
  (visit_nat an bn can cbn)
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

Definition visit_prop(x:prop_expr)(c0 c:config_expr):option N :=
match x with
| (_,[multistep_lb_expr a b _]) => visit_config a b c0 c
| _ => None
end.

End Visit3.

Definition min_ind_n:N := 0.
Definition find_IH(x:prop_expr)(i:id_t)(x0' x0:prop_expr):option (prop_expr'*(prop_expr')*_*option N) :=
match x,x0',x0 with
| (Hx,[a]),([],[multistep'_expr _ c' _]),([],[multistep'_expr _ c _]) =>
  match Visit1.visit_prop0 a c' c with
  | None => None
  | Some (a,b,H) =>
    match solve_assumptions solve_assumptions_iter_limit TrySubst.config_normal (H++Hx,[multistep'_expr a b false]) i with
    | Some (Hx',[multistep'_expr a b false],mp) =>
      let w0 := (simpl_rule (Hx',[multistep_lb_expr a b nat_ivar])) in
      let n := Visit3.visit_prop (fst w0) c' c in
      let (b',p) :=
      match n with
      | None => Visit2.visit_config' c 1%positive
      | Some n => Visit2.visit_config' c 1%positive (*Visit2.visit_config n a b c' c 1%positive*)
      end in
      let w1 := ([],[multistep'_expr b' b' false],p) in
      match n with
      | None =>
        match follow_rule ([],[multistep_lb_expr c' c' (from_nat 0)],1%positive) w0 with
        | Some w0' => Some (simpl_rule (fst w0'),w1,mp,n)
        | None => None
        end
      | Some n0 => if (n0 <? min_ind_n)%N then None else Some (w0,w1,mp,n)
      end
    | _ => None
    end
  end
| _,_,_ => None
end.

End FindIH.



Record Config := {
  max_repeater_len:nat;
  max_repeater_size:option N;
  fixed_block_size:option nat;
  enable_arithseq:bool;
  initial_steps:N;
  mnc:N;
}.
Definition default_config := {|
  max_repeater_len := 8;
  max_repeater_size := None;
  fixed_block_size := None;
  enable_arithseq := false;
  initial_steps := 0;
  mnc := 0;
|}.
Definition config_limited_repeater_size := {|
  max_repeater_len := 8;
  max_repeater_size := Some 16%N;
  fixed_block_size := None;
  enable_arithseq := false;
  initial_steps := 0;
  mnc := 0;
|}.
Definition config_arithseq n := {|
  max_repeater_len := 8;
  max_repeater_size := Some 16%N;
  fixed_block_size := None;
  enable_arithseq := true;
  initial_steps := n;
  mnc := 0;
|}.
Definition config_arithseq_fixed_block_size T0 n := {|
  max_repeater_len := 16;
  max_repeater_size := Some (N.of_nat n);
  fixed_block_size := Some n;
  enable_arithseq := true;
  initial_steps := T0;
  mnc := 2;
|}.

Section tm_ctx.
Hypothesis tm:TM.
Hypothesis cfg:Config.

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

Definition seg_arithseq_entry_to_seg(n1 n2:nat)(x:(list Sym)*Z*nat_expr):list Sym :=
let '(x0,x1,x2):=x in
let x2 := N.to_nat (to_nat x2) in
match x1 with
| Zpos x1 => x0 ^^ ((Pos.to_nat x1)*n1+x2)
| Zneg x1 => x0 ^^ ((Pos.to_nat x1)*n2+x2)
| Z0 => x0
end.

Fixpoint seg_arithseq_to_seg a n n2:list Sym :=
match n with
| O => nil
| Datatypes.S n0 =>
  (flat_map (seg_arithseq_entry_to_seg n0 n2) a) ++
  seg_arithseq_to_seg a n0 (Datatypes.S n2)
end.

Fixpoint to_seg(x:seg_expr):list Sym :=
match x with
| seg_nil => []
| seg_sym a => [a]
| seg_concat a b => (to_seg a) ++ (to_seg b)
| seg_repeat a n => (to_seg a) ^^ (N.to_nat (to_nat n))
| seg_arithseq a n => seg_arithseq_to_seg a (N.to_nat (to_nat n)) O
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
| multistep_lb_expr x0 x1 n => multistep_lb tm (N.to_nat (to_nat n)) (to_config x0) (to_config x1)
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
  - rewrite Forall_app in E.
    rewrite (solve_nat_eq_spec n n0). 2: tauto.
    generalize 0.
    induction (N.to_nat (to_nat n0)); intros n2.
    1: reflexivity.
    cbn.
    f_equal.
    2: apply IHn1. clear IHn1.
    destruct E as [E _].
    gen a0.
    induction a as [|a1 a]; intros a0; destruct a0 as [|a2 a0].
    + cbn.
      tauto.
    + cbn.
      rewrite Forall_cons_iff; cbn; tauto.
    + cbn.
      destruct a1 as [[a11 a12] a13].
      rewrite Forall_cons_iff; cbn; tauto.
    + cbn.
      destruct a1 as [[a11 a12] a13].
      destruct a2 as [[a21 a22] a23].
      destruct (list_eqb_spec sym_eqb a11 a21).
      1: apply sym_eqb_spec.
      2: rewrite Forall_cons_iff; cbn; tauto.
      destruct (Z.eqb_spec a12 a22).
      2: rewrite Forall_cons_iff; cbn; tauto.
      subst.
      rewrite Forall_app.
      intros [H1 H2].
      rewrite (IHa a0 H2).
      pose proof (solve_nat_eq_spec _ _ H1) as H1'.
      cbn in H1'.
      cbn.
      rewrite H1'. reflexivity.
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
  - intros [H1 H2].
    erewrite ExprEq_nat_spec; eauto.
    generalize 0.
    induction (N.to_nat (to_nat n0)); intros n2.
    1: reflexivity.
    cbn.
    rewrite IHn1. clear IHn1.
    f_equal.
    gen a0.
    induction a as [|a0 a]; intros [|a2 a1]; cbn; try congruence.
    intro H.
    rewrite and_true_iff in H.
    destruct H as [H H0].
    specialize (IHa _ H0).
    rewrite IHa.
    f_equal.
    destruct a0 as [[a01 a02] a03].
    destruct a2 as [[a21 a22] a23].
    cbn. cbn in H.
    repeat rewrite and_true_iff in H.
    destruct H as [[H H2] H3].
    destruct (list_eqb_spec sym_eqb a01 a21 sym_eqb_spec); try congruence.
    destruct (Z.eqb_spec a02 a22); try congruence.
    subst.
    rewrite (ExprEq_nat_spec _ _ H3).
    reflexivity.
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
  - rewrite (nat_simpl_spec n).
    congruence.
  - rewrite (nat_simpl_spec n).
    generalize 0.
    induction (N.to_nat (to_nat n)); intros n2.
    1: reflexivity.
    cbn.
    rewrite IHn0. clear IHn0.
    f_equal.
    induction a.
    1: reflexivity.
    cbn.
    rewrite IHa.
    f_equal.
    destruct a as [[x0 x1] x2]; cbn.
    rewrite nat_simpl_spec.
    reflexivity.
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
  - reflexivity.
  - cbn.
    rewrite IHx1,IHx2.
    reflexivity.
  - cbn.
    rewrite IHx,nat_subst_spec.
    reflexivity.
  - cbn.
    rewrite nat_subst_spec.
    unfold mpi. cbn.
    generalize 0.
    induction (N.to_nat (to_nat mp (to_nat mp' mpi' mpi0) n)); intros n2.
    1: reflexivity.
    cbn.
    rewrite IHn0. clear IHn0.
    f_equal.
    induction a as [|a0 a].
    1: reflexivity.
    cbn.
    rewrite IHa.
    f_equal.
    destruct a0 as [[a0 a1] a2]; cbn.
    rewrite nat_subst_spec.
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

Lemma multistep_lb_trans n1 n2 s1 s2 s3:
  multistep_lb tm n1 s1 s2 ->
  multistep_lb tm n2 s2 s3 ->
  multistep_lb tm (n1+n2) s1 s3.
Proof.
  unfold multistep_lb.
  intros [n1' [H1a H1b]] [n2' [H2a H2b]].
  exists (n1'+n2').
  split. 1: lia.
  eapply multistep_trans; eauto.
Qed.








Definition match_prop(x1 x2:prop_expr):option prop_expr :=
match x1,x2 with
| ([],[multistep_lb_expr s1 s2 n1]),([],[multistep_lb_expr s1' s2' n1']) =>
  Some ([config_eq s1 s1';config_eq s2 s2';nat_eq n1 n1'],[])
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
  prove induction step by "follow IH; follow wS; finish"
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
| (multistep_lb_expr a b n)::_ => Some b
| (multistep'_expr a b n)::_ => Some b
| _ => None
end.

Definition get_config_l(x:prop_expr') :=
let '((H,G),i):=x in
match G with
| (multistep_lb_expr a b n)::_ => Some a
| (multistep'_expr a b n)::_ => Some a
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

Definition step01_to_lb(x:prop_expr'):prop_expr' :=
match x with
| (H,(multistep'_expr a b n)::G,i) =>
  (H,(multistep_lb_expr a b (from_nat (if n then 1 else 0)))::G,i)
| _ => x
end.

Definition lb_to_step0(x:prop_expr'):prop_expr' :=
match x with
| (H,(multistep_lb_expr a b n)::G,i) =>
  (H,(multistep'_expr a b false)::G,i)
| _ => x
end.

Definition is_const(x:prop_expr'):bool :=
match x with
| ([],G,1%positive) => true
| _ => false
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

Fixpoint to_nat_const(x:nat_expr):option N :=
match x with
| from_nat n => Some n
| nat_add a b =>
  match to_nat_const a,to_nat_const b with
  | Some a0,Some b0 => Some (a0+b0)%N
  | _,_ => None
  end
| nat_mul a b =>
  match to_nat_const a,to_nat_const b with
  | Some a0,Some b0 => Some (a0*b0)%N
  | _,_ => None
  end
| _ => None
end.

Section TryInd.
Hypothesis mnc:N.
Definition subst_small_vars(mp:list (PositiveMap.tree expr_expr))(i:id_t)(t:type_t):to_expr_type t :=
match t as t0 return (to_expr_type t0) with
| nat_t =>
    match to_nat_const (subst_list_map mp i nat_t) with
    | Some n => if (n<?mnc)%N then from_nat n else mk_var i _
    | None => mk_var i _
    end
| _ => mk_var i _
end.
(* when a var < mnc, specialize it
  this increases readability of some rules, but may not solve more TMs
 *)
Definition subst_small_vars_for_follow(w0 w1 w1':prop_expr'):option prop_expr' :=
if (mnc =? N0)%N then Some w1' else
match get_config_r w0,get_config_l w1 with
| Some c0,Some c1 =>
  match solve_assumptions solve_assumptions_iter_limit TrySubst.config_normal (config_eq c0 c1 :: fst (fst w1),[]) (snd w1)%positive with
  | None => None
  | Some (x,mp) =>
    Some (simpl_rule (SubstExpr.subst_prop (subst_small_vars mp) nat_ivar (fst w1')))
  end
| _,_ => None
end.

Definition subst_ind_S(w:prop_expr') (mp:list (PositiveMap.tree expr_expr)):prop_expr' :=
  let w1 := w in
  (SubstExpr.subst_prop (subst_list_map mp) nat_ivar (fst w1),snd w1).

(*
  find accelerate rule w1^n, that can be used after w0
  input (w1, w0, w0 w1)
  output ((forall n, w1^n), w0 w1^n)
  if proved nonhalt, w0 w1^n is multistep_lb, else w0 w1^n is multistep'
*)
Definition try_ind(w1 w0' w0:prop_expr'):option (prop_expr'*prop_expr') :=
let (x1,i1):=w1 in
match FindIH.find_IH x1 i1 (fst w0') (fst w0) with
| Some (w2,x3,mp,n) =>
  match (find_step0_refl w1) with
  | None => None
  | Some w10 =>
    let w1' := subst_ind_S w1 mp in
    if solve_ind (step01_to_lb w10) (step01_to_lb w1') w2 then
      match n with
      | Some n =>
        if solve_apply w10 x3 then
          let w2 := (lb_to_step0 w2) in
          match follow_rule w2 x3 with
          | None => None
          | Some w2 =>
            let w2n := (specialize_ivar w2 n) in
            match subst_small_vars_for_follow w0' w2n w2 with
            | None => None
            | Some w2 =>
              match follow_rule w0' w2n with
              | None => None
              | Some w0 => if is_const w0 then Some (remove_ivar w2,w0) else None
              end
            end
          end
        else None
      | None =>
        match follow_rule (step01_to_lb (step1_to_step0 w0')) (remove_ivar w2) with
        | None => None
        | Some w0 =>
          let w2 := (lb_to_step0 w2) in
          Some (remove_ivar w2,w0)
        end
      end
    else None
  end
| _ => None
end.
End TryInd.

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
{
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

  rewrite Nnat.N2Nat.inj_add.
  eapply multistep_lb_trans; eauto.
}
{
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
}
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


Lemma try_subst_spec cfg0 x i:
  let '((x',i'),_):=(TrySubst.try_subst cfg0 x i) in
  (to_prop'' x) -> (to_prop'' x').
Proof.
  destruct x as [H G].
  cbn.
  destruct (TrySubst.list_find_subst cfg0 H (PositiveMap.empty expr_expr, PositiveMap.empty unit, i)) as [[sl _] _].
  intros H0.
  apply (subst_spec (H,G)),H0.
Qed.

Lemma solve_assumptions_spec n cfg0 x i:
to_prop'' x ->
match solve_assumptions n cfg0 x i with
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
  pose proof (try_subst_spec cfg0 (prop_solve_eq x) i) as H1.
  destruct (TrySubst.try_subst cfg0 (prop_solve_eq x) i) as [[x0 i0] mp0].
  specialize (H1 H0).
  destruct (list_prop0_eqb (fst x0) []).
  1: tauto.
  destruct (prop_eqb x0 x).
  1: trivial.
  specialize (IHn x0 i0 H1).
  destruct (solve_assumptions n cfg0 x0 i0) as [[]|]; trivial.
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
  all: repeat rewrite to_nat_fext; try congruence.
  generalize 0.
  induction (N.to_nat (to_nat mp' mpi n)); intro n2; cbn.
  1: reflexivity.
  rewrite IHn0. clear IHn0.
  f_equal.
  induction a as [|[[a0 a1] a2] a].
  1: reflexivity.
  cbn.
  rewrite IHa.
  rewrite to_nat_fext.
  reflexivity.
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

Lemma multistep_evstep a b n:
  a -[ tm ]->> n / b ->
  a -[ tm ]->* b.
Proof.
  gen a b.
  induction n; intros.
  - inverts H.
    trivial.
  - inverts H.
    eapply evstep_step; eauto.
Qed.

Lemma evstep_multistep_lb a b:
  a -[ tm ]->* b ->
  multistep_lb tm 0 a b.
Proof.
  intro H.
  induction H.
  - exists 0; split. 1: lia.
    constructor.
  - destruct IHevstep as [n [H1 H2]].
    exists (1+n).
    split. 1: lia.
    cbn.
    econstructor; eauto.
Qed.

Lemma progress_multistep_lb a b:
  a -[ tm ]->+ b ->
  multistep_lb tm 1 a b.
Proof.
  intro H.
  induction H.
  - exists 1; split. 1: lia.
    econstructor; eauto.
  - destruct IHprogress as [n [H1 H2]].
    exists (1+n).
    split. 1: lia.
    cbn.
    econstructor; eauto.
Qed.

Lemma lb_to_step0_spec w:
  to_prop' (fst w) ->
  to_prop' (fst (lb_to_step0 w)).
Proof.
  destruct w as [[H G] i].
  destruct G as [|[] G]; try tauto.
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
  intros [n0 [H0 H1]].
  eapply multistep_evstep; eauto.
Qed.

Lemma step01_to_lb_spec w:
  to_prop' (fst w) ->
  to_prop' (fst (step01_to_lb w)).
Proof.
  destruct w as [[H G] i].
  destruct G as [|[] G]; try tauto.
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
  gen H1; cbn.

  destruct n; intro H1.
  - apply progress_multistep_lb,H1.
  - apply evstep_multistep_lb,H1.
Qed.

Lemma subst_ind_S_spec w mp:
  to_prop' (fst w) ->
  to_prop' (fst (subst_ind_S w mp)).
Proof.
  intro H.
  cbn.
  intros mpi.
  apply subst_spec,H.
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

Lemma subst_small_vars_for_follow_spec mnc w0 w1 w2:
  to_prop' (fst w0) ->
  to_prop' (fst w1) ->
  to_prop' (fst w2) ->
  match subst_small_vars_for_follow mnc w0 w1 w2 with
  | None => True
  | Some w => to_prop' (fst w)
  end.
Proof.
  intros H0 H1 H2.
  unfold subst_small_vars_for_follow.
  destruct_spec N.eqb. 1: tauto.
  destruct_spec get_config_r; trivial.
  destruct_spec get_config_l; trivial.
  destruct_spec solve_assumptions; trivial.
  destruct p as [_ mp].
  intro mpi.
  apply (simpl_rule_spec mpi).
  apply subst_spec.
  apply H2.
Qed.

Lemma try_ind_spec mnc w1 w0' w0:
  to_prop' (fst w1) ->
  to_prop' (fst w0') ->
  match try_ind mnc w1 w0' w0 with
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
    - apply step01_to_lb_spec,H.
    - apply step01_to_lb_spec,subst_ind_S_spec,H'.
  }
  destruct n as [n|].
  - destruct_spec solve_apply_spec'; trivial.
    destruct_spec follow_rule_spec'; trivial.
    destruct_spec subst_small_vars_for_follow_spec; trivial.
    destruct_spec follow_rule_spec'; trivial.
    pose proof (lb_to_step0_spec x2).
    pose proof (specialize_ivar_spec p0 n).
    destruct_spec is_const; trivial.
    split.
    + apply remove_ivar_spec. tauto.
    + tauto.
  - destruct_spec follow_rule_spec'; trivial.
    split.
    + apply remove_ivar_spec,lb_to_step0_spec,H1.
    + apply H2; try tauto.
      2: apply remove_ivar_spec,H1.
      apply step01_to_lb_spec,step1_to_step0_spec,H0'.
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

Definition seg_concat_def(r0:seg_expr):=
  let r:=side_var 1%positive in
  (side_eq
  (side_concat r0 r)
  (side_concat_unfold r0 r),
  2%positive).

Lemma seg_concat_def_spec r0:
  to_prop0' (fst (seg_concat_def r0)).
Proof.
  unfold to_prop0'.
  intros.
  cbn.
  rewrite side_concat_unfold_spec.
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


Fixpoint to_seg_const(x:seg_expr):option (list Sym) :=
match x with
| seg_nil => Some []
| seg_sym a => Some [a]
| seg_concat a b =>
  match to_seg_const a,to_seg_const b with
  | Some a',Some b' => Some (a'++b')
  | _,_ => None
  end
| seg_repeat a (from_nat n) =>
  match to_seg_const a with
  | Some a' => Some (a' ^^ (N.to_nat n))
  | None => None
  end
| _ => None
end.

Lemma to_seg_const_spec x mp mpi:
match to_seg_const x with
| Some x0 => to_seg mp mpi x = x0
| None => True
end.
Proof.
  induction x; cbn; trivial.
  - destruct_spec to_seg_const; trivial.
    destruct_spec to_seg_const; trivial.
    congruence.
  - destruct n; trivial.
    destruct_spec to_seg_const; trivial.
    cbn.
    congruence.
Qed.

Fixpoint from_seg(x:list Sym):seg_expr :=
match x with
| nil => seg_nil
| h::t => 
  match t with
  | nil => seg_sym h
  | _ => seg_concat (seg_sym h) (from_seg t)
  end
end.

Lemma from_seg_spec x0 mp mpi:
  to_seg mp mpi (from_seg x0) = x0.
Proof.
  induction x0.
  1: reflexivity.
  destruct x0.
  1: reflexivity.
  cbn.
  cbn in IHx0.
  congruence.
Qed.

Fixpoint side_concat_list_seg(r0:list seg_expr)(r:side_expr):side_expr :=
match r0 with
| r1::r2 => side_concat r1 (side_concat_list_seg r2 r)
| nil => r
end.

Lemma side_concat_list_seg_spec mp mpi r0 r:
  to_side mp mpi (side_concat_list_seg r0 r) =
  flat_map (to_seg mp mpi) r0 *> to_side mp mpi r.
Proof.
  induction r0.
  1: reflexivity.
  cbn.
  rewrite Str_app_assoc.
  congruence.
Qed.

Definition seg_arithseq_entry_S(n:nat_expr)(x:seg_expr*Z*N)(p:id_t):
  option (((list Sym)*Z*nat_expr)*((list Sym)*Z*nat_expr)*seg_expr*id_t) :=
let '(x0',x1,x2):=x in
match to_seg_const x0' with
| None => None
| Some x0 =>
  Some (
  let (v,p) := (nat_var p,Pos.succ p) in
  match x1 with
  | Zpos x1' =>
    let v:=(from_nat x2) in
    ((x0,x1,v),(x0,x1,v),seg_repeat x0' (nat_add v (nat_mul n (from_nat (Npos x1')))),p)
  | Zneg x1' => ((x0,x1,v),(x0,x1,nat_add v (from_nat (Npos x1'))),seg_repeat x0' v,p)
  | Z0 => ((x0,x1,v),(x0,x1,v),x0',p)
  end)
end.

Fixpoint seg_arithseq_S(n:nat_expr)(x:list (seg_expr*Z*N))(p:id_t):
  option ((list ((list Sym)*Z*nat_expr))*(list ((list Sym)*Z*nat_expr))*(list seg_expr)*id_t) :=
match x with
| nil => Some (nil,nil,nil,p)
| h::t =>
  match seg_arithseq_S n t p with
  | Some (b0,b1,b2,p) =>
    match seg_arithseq_entry_S n h p with
    | Some (a0,a1,a2,p) => Some (a0::b0,a1::b1,a2::b2,p)
    | None => None
    end
  | None => None
  end
end.

Definition arithseq_S_def(r0:list (seg_expr*Z*N)):=
  let n:=nat_var 1%positive in
  let r:=side_var 2%positive in
  match seg_arithseq_S n r0 (3%positive) with
  | None => None
  | Some (r1,r2,r3,p) =>
    Some
    (side_eq
    (side_concat (seg_arithseq r1 (nat_add n (from_nat 1))) r)
    (side_concat_list_seg r3 (side_concat (seg_arithseq r2 n) r)),
    p)
  end.

Lemma arithseq_S_def_spec r0:
  match arithseq_S_def r0 with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  unfold to_prop0'.
  destruct (arithseq_S_def r0) as [[x' p']|] eqn:E'; trivial.
  intros mp mpi.
  cbn.
  unfold arithseq_S_def in E'.
  destruct (seg_arithseq_S (nat_var 1%positive) r0 3%positive) as [[[[r1 r2] r3] p]|] eqn:E.
  2: congruence.
  inverts E'.
  cbn.
  rewrite Nnat.N2Nat.inj_add.
  rewrite Nat.add_comm.
  change (N.to_nat 1) with 1. cbn.
  rewrite side_concat_list_seg_spec.
  rewrite Str_app_assoc.
  cbn.
  f_equal.
{
  gen r1 r2 r3 p'.
  induction r0; intros.
  - cbn in E. inverts E. reflexivity.
  - cbn in E.
    destruct (seg_arithseq_S (nat_var 1%positive) r0 3%positive) as [[[[b0 b1] b2] p1]|] eqn:E1.
    2: congruence.
    destruct (seg_arithseq_entry_S (nat_var 1%positive) a p1) as [[[[a0 a1] a2] p2]|] eqn:E2.
    2: congruence.
    inverts E.
    cbn.
    erewrite IHr0. 2: reflexivity.
    f_equal.
    destruct a as [[x0 x1] x2].
    cbn in E2.
    pose proof (to_seg_const_spec x0) as H3.
    destruct (to_seg_const x0) as [x0'|] eqn:E3.
    2: congruence.
    destruct x1 as [|x1|x1];
    inverts E2; cbn;
    rewrite H3.
    2,3: f_equal; lia.
    reflexivity.
}
{
  gen r0 r1 r2 r3 p'.
  generalize 0.
  induction (N.to_nat (mp 1%positive nat_t)); intros.
  1: reflexivity.
  cbn.
  repeat rewrite Str_app_assoc.
  erewrite (IHn (Datatypes.S n0)). 2: apply E.
  f_equal.
  gen r1 r2 r3 p'.
  induction r0; intros.
  - cbn in E. inverts E.
    reflexivity.
  - cbn in E.
    destruct (seg_arithseq_S (nat_var 1%positive) r0 3%positive) as [[[[b0 b1] b2] p1]|] eqn:E1.
    2: congruence.
    destruct (seg_arithseq_entry_S (nat_var 1%positive) a p1) as [[[[a0 a1] a2] p2]|] eqn:E2.
    2: congruence.
    inverts E.
    cbn.
    erewrite IHr0. 2: reflexivity.
    f_equal.
    destruct a as [[x0 x1] x2].
    cbn in E2.
    pose proof (to_seg_const_spec x0) as H3.
    destruct (to_seg_const x0) as [x0'|] eqn:E3.
    2: congruence.
    destruct x1 as [|x1|x1]; inverts E2; cbn.
    2,3: f_equal; lia.
    reflexivity.
}
Qed.

Definition seg_arithseq_entry_3(x:seg_expr*Z*N)(p:id_t):
  option (seg_expr*seg_expr*seg_expr*((list Sym)*Z*nat_expr)*id_t) :=
let '(x0',x1,x2):=x in
match to_seg_const x0' with
| None => None
| Some x0 =>
  Some (
  let (v,p) := (nat_var p,Pos.succ p) in
  match x1 with
  | Zpos x1' =>
    (seg_repeat x0' (from_nat (x2+Npos x1'+Npos x1')),
     seg_repeat x0' (from_nat (x2+Npos x1')),
     seg_repeat x0' (from_nat x2),
    (x0,x1,(from_nat x2)),p)
  | Zneg x1' =>
    (seg_repeat x0' v,
     seg_repeat x0' (nat_add v (from_nat (Npos x1'))),
     seg_repeat x0' (nat_add v (from_nat (Npos x1'+Npos x1'))),
    (x0,x1,v),p)
  | Z0 => (x0',x0',x0',(x0,x1,(from_nat 0)),p)
  end)
end.

Fixpoint seg_arithseq_3(x:list (seg_expr*Z*N))(p:id_t):
  option ((list seg_expr)*(list seg_expr)*(list seg_expr)*(list ((list Sym)*Z*nat_expr))*id_t) :=
match x with
| nil => Some (nil,nil,nil,nil,p)
| h::t =>
  match seg_arithseq_3 t p with
  | Some (b0,b1,b2,b3,p) =>
    match seg_arithseq_entry_3 h p with
    | Some (a0,a1,a2,a3,p) => Some (a0::b0,a1::b1,a2::b2,a3::b3,p)
    | None => None
    end
  | None => None
  end
end.

Definition arithseq_3_def(r0:list (seg_expr*Z*N)):=
  let n:=nat_var 1%positive in
  let r:=side_var 2%positive in
  match seg_arithseq_3 r0 (3%positive) with
  | None => None
  | Some (r1,r2,r3,r4,p) =>
    Some
    (side_eq
    (side_concat (seg_arithseq r4 (from_nat 3)) r)
    (side_concat_list_seg (r1++r2++r3) r),
    p)
  end.

Lemma arithseq_3_def_spec r0:
  match arithseq_3_def r0 with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  unfold to_prop0'.
  destruct (arithseq_3_def r0) as [[x' p']|] eqn:E'; trivial.
  intros mp mpi.
  cbn.
  unfold arithseq_3_def in E'.
  destruct (seg_arithseq_3 r0 3%positive) as [[[[[r1 r2] r3] r4] p]|] eqn:E.
  2: congruence.
  inverts E'.
  cbn.
  rewrite side_concat_list_seg_spec.
  repeat rewrite flat_map_app.
  change (Pos.to_nat 3) with 3.
  cbn.
  repeat rewrite Str_app_assoc.
  cbn.
  f_equal; [|f_equal; [|f_equal]];
  gen r1 r2 r3 r4 p';
  (induction r0; intros;
  [ cbn in E; inverts E; reflexivity |]);
  cbn in E;
  destruct (seg_arithseq_3 r0 3%positive) as [[[[[b0 b1] b2] b3] p1]|] eqn:E1;
  try congruence;
  destruct (seg_arithseq_entry_3 a p1) as [[[[[a0 a1] a2] a3] p2]|] eqn:E2;
  try congruence;
  inverts E;
  cbn;
  erewrite IHr0; try reflexivity;
  f_equal;
  destruct a as [[x0 x1] x2];
  cbn in E2;
  pose proof (to_seg_const_spec x0) as H3;
  destruct (to_seg_const x0) as [x0'|];
  try congruence;
  destruct x1 as [|x1|x1];
  inverts E2; cbn;
  rewrite H3; try reflexivity;
  f_equal; lia.
Qed.


Fixpoint generalize_arithseq (ls:list ((list Sym) * Z * nat_expr))(p:id_t) :=
match ls with
| nil => (nil,p)
| (x0,x1,x2)::t =>
  let (t,p):=generalize_arithseq t p in
  ((x0,x1,nat_var p)::t,Pos.succ p)
end.

Definition arithseq_0_def r0 :=
  let (r0,p):=generalize_arithseq r0 (1%positive) in
  let (r,p):=(side_var p,Pos.succ p) in
  (side_eq
  (side_concat (seg_arithseq r0 (from_nat 0)) r)
  r,
  p).

Lemma arithseq_0_def_spec r0:
  to_prop0' (fst (arithseq_0_def r0)).
Proof.
  unfold to_prop0'.
  unfold arithseq_0_def.
  destruct (generalize_arithseq r0 1%positive).
  reflexivity.
Qed.

Definition arithseq_0_def' r0 :=
  let (r0,p):=generalize_arithseq r0 (1%positive) in
  let (r,p):=(side_var p,Pos.succ p) in
  (side_eq
  r
  (side_concat (seg_arithseq r0 (from_nat 0)) r),
  p).

Lemma arithseq_0_def_spec' r0:
  to_prop0' (fst (arithseq_0_def' r0)).
Proof.
  unfold to_prop0'.
  unfold arithseq_0_def'.
  destruct (generalize_arithseq r0 1%positive).
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

Definition seg_find_arithseq_3_fold(h1 h2 h3:seg_expr):=
if seg_expr_eqb h1 h2 && seg_expr_eqb h1 h3 then
  Some (h1,Z0,N0)
else
match h1,h2,h3 with
| seg_repeat a1 (from_nat n1),seg_repeat a2 (from_nat n2),seg_repeat a3 (from_nat n3) =>
  if seg_expr_eqb a1 a2 && seg_expr_eqb a1 a3 && (n1+n3 =? n2*2)%N then
    if (n1 <? n2)%N then
      Some (a1,Z.opp (Z.of_N (n2-n1)%N),n1)
    else
      Some (a1,Z.of_N (n1-n2)%N,n3)
  else None
| _,_,_ => None
end.

Fixpoint side_find_arithseq_3_fold(ls1 ls2 ls3:side_expr)(n:nat):=
match n with
| O => Some []
| Datatypes.S n0 =>
  match ls1,ls2,ls3 with
  | side_concat h1 t1,side_concat h2 t2,side_concat h3 t3 =>
    match seg_find_arithseq_3_fold h1 h2 h3 with
    | Some v1 =>
      match side_find_arithseq_3_fold t1 t2 t3 n0 with
      | Some v => Some (v1::v)
      | None => None
      end
    | None => None
    end
  | _,_,_ => None
  end
end.

Fixpoint arithseq_has_var (ls:list ((seg_expr)*Z*N)):bool :=
match ls with
| nil => false
| (x0,x1,x2)::t => negb (x1 =? Z0)%Z || arithseq_has_var t
end.

Definition side_find_arithseq_3_fold' ls1 ls2 ls3 n :=
match side_find_arithseq_3_fold ls1 ls2 ls3 n with
| None => None
| Some ls =>
  if arithseq_has_var ls then Some ls else None
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

Definition seg_check_arithseq_S_fold(h1:seg_expr)(h2:((list Sym)*Z*nat_expr))(n:N) :=
match h1,h2 with
| seg_repeat x0' (from_nat x2'),(x0,Zpos x1,from_nat x2) =>
  match to_seg_const x0' with
  | Some x0'' =>
    if list_eqb sym_eqb x0'' x0 && (x2' =? x2+(Npos x1)*n)%N then
      Some (x0',Zpos x1,x2)
    else None
  | _ => None
  end
| seg_repeat x0' (from_nat x2'),(x0,Zneg x1,from_nat x2) =>
  match to_seg_const x0' with
  | Some x0'' =>
    if list_eqb sym_eqb x0'' x0 && (x2'+(Npos x1) =? x2)%N then
      Some (x0',Zneg x1,x2')
    else None
  | _ => None
  end
| x0',(x0,Z0,_) =>
  match to_seg_const x0' with
  | Some x0'' =>
    if list_eqb sym_eqb x0'' x0 then
      Some (x0',Z0,N0)
    else None
  | _ => None
  end
| _,_ => None
end.

Fixpoint side_check_arithseq_S_fold(ls1:side_expr)(ls2:list ((list Sym)*Z*nat_expr))(n:nat)(n':N):=
match n,ls2 with
| O,[] => Some []
| Datatypes.S n0,h2::t2 =>
  match ls1 with
  | side_concat h1 t1 =>
    match seg_check_arithseq_S_fold h1 h2 n' with
    | None => None
    | Some v1 =>
      match side_check_arithseq_S_fold t1 t2 n0 n' with
      | None => None
      | Some v => Some (v1::v)
      end
    end
  | _ => None
  end
| _,_ => None
end.

Definition side_find_repeat_S_fold ls1 ls2 n :=
match ls2 with
| side_concat (seg_repeat h2 _) _ =>
  if side_check_repeat_S_fold ls1 h2 n then Some h2 else None
| _ => None
end.

Definition side_find_arithseq_S_fold ls1 ls2 n :=
match ls2 with
| side_concat (seg_arithseq h2 (from_nat n')) _ =>
  side_check_arithseq_S_fold ls1 h2 n n'
| _ => None
end.

Definition side_find_repeat_O_fold ls :=
match ls with
| side_concat (seg_repeat h (from_nat 0)) _ => Some (repeat_0_def' h)
| side_concat (seg_arithseq h (from_nat 0)) _ => Some (arithseq_0_def' h)
| _ => None
end.


Fixpoint get_seg_size_lb(x:seg_expr):N :=
match x with
| seg_sym _ => 1%N
| seg_concat a b => (get_seg_size_lb a + get_seg_size_lb b)%N
| seg_repeat a (from_nat n) => ((get_seg_size_lb a)*n)%N
| _ => 0%N
end.

Definition check_seg_size(x:seg_expr):bool :=
match cfg.(max_repeater_size) with
| None => true
| Some n => (get_seg_size_lb x <=? n)%N
end.

Definition side_find_repeat_fold_1 ls1 ls2 n :=
match side_find_repeat_2_fold ls1 ls2 n with
| Some h => if check_seg_size h then Some (repeat_2_def h) else None
| None =>
  match side_find_repeat_S_fold ls1 ls2 n with
  | Some h => Some (repeat_S_def h)
  | None => None
  end
end.

Definition side_find_arithseq_fold_1 ls1 ls2 ls3 n :=
match n with
| O => None
| _ =>
  match side_find_arithseq_3_fold' ls1 ls2 ls3 n with
  | Some h => arithseq_3_def h
  | None =>
    match side_find_arithseq_S_fold ls1 ls2 n with
    | Some h => arithseq_S_def h
    | None => None
    end
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

Definition side_tl(x:side_expr):=
match x with
| side_concat _ t => t
| _ => x
end.

Fixpoint side_find_arithseq_fold_2 ls1 ls2 ls3 n n0 {struct n0} :=
match n0 with
| O => None
| Datatypes.S n1 =>
  match side_find_arithseq_fold_1 ls1 ls2 ls3 n with
  | Some h => Some h
  | None =>
    match ls2 with
    | side_concat _ t2 =>
      side_find_arithseq_fold_2 ls1 t2 (side_tl (side_tl ls3)) (Datatypes.S n) n1
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

Definition side_concat_rw_2'(x:prop0_expr*id_t)(v:seg_expr):prop0_expr*id_t :=
side_concat_rw_2 x.

Lemma side_concat_rw_2_spec' x v:
  to_prop0' (fst x) ->
  to_prop0' (fst (side_concat_rw_2' x v)).
Proof.
  apply side_concat_rw_2_spec.
Qed.
(*
Definition side_concat_rw_2'(x:prop0_expr*id_t)(v:seg_expr):prop0_expr*id_t :=
match x with
| (side_eq a b,p) =>
  (side_eq (side_concat v a) (side_concat v b),p)
| _ => x
end.

Lemma side_concat_rw_2_spec' x v:
  to_prop0' (fst x) ->
  to_prop0' (fst (side_concat_rw_2' x v)).
Proof.
  unfold to_prop0'.
  destruct x as [x i].
  cbn.
  intros H mp mpi.
  specialize (H mp mpi).
  destruct x; cbn; cbn in H; congruence.
Qed.
*)
Definition is_seg_repeat(x:seg_expr) :=
match x with
| seg_repeat _ _ => true
| _ => false
end.

Fixpoint side_find_repeat_fold_dynlen ls1 :=
match side_find_repeat_O_fold ls1 with
| Some h => Some h
| None =>
  match ls1 with
  | side_concat h1 t1 =>
    match side_find_repeat_fold_dynlen t1 with
    | Some v => Some (side_concat_rw_2' v h1)
    | None =>
      match side_find_repeat_fold_2 ls1 ls1 O cfg.(max_repeater_len) with
      | Some v => Some v
      | None =>
        if cfg.(enable_arithseq) then
          match side_find_arithseq_fold_2 ls1 ls1 ls1 O cfg.(max_repeater_len) with
          | Some v => Some v
          | None => None
          end
        else None
      end
    end
  | _ => None
  end
end.

Fixpoint side_find_repeat_fold_fixedlen ls1 ls2 n :=
match side_find_repeat_O_fold ls1 with
| Some h => Some h
| None =>
  match ls1 with
  | side_concat h1 t1 =>
    match side_find_repeat_fold_fixedlen t1 (side_tl ls2) n with
    | Some v => Some (side_concat_rw_2' v h1)
    | None =>
      match side_find_repeat_fold_1 ls1 ls2 n with
      | Some v => Some v
      | None =>
        if cfg.(enable_arithseq) && is_seg_repeat h1 then
          match side_find_arithseq_fold_2 ls1 ls1 ls1 O cfg.(max_repeater_len) with
          | Some v => Some v
          | None => None
          end
        else None
      end
    end
  | _ => None
  end
end.

Definition side_find_repeat_fold ls :=
match cfg.(fixed_block_size) with
| None => side_find_repeat_fold_dynlen ls
| Some n => side_find_repeat_fold_fixedlen ls (Nat.iter n side_tl ls) (Nat.pred n)
end.

Lemma side_find_repeat_fold_1_spec ls1 ls2 n:
  match side_find_repeat_fold_1 ls1 ls2 n with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  unfold side_find_repeat_fold_1.
  destruct (side_find_repeat_2_fold ls1 ls2 n).
  1: destruct_spec check_seg_size; trivial.
  1: apply repeat_2_def_spec.
  destruct (side_find_repeat_S_fold ls1 ls2 n).
  1: apply repeat_S_def_spec.
  trivial.
Qed.

Lemma side_find_arithseq_fold_1_spec ls1 ls2 ls3 n:
  match side_find_arithseq_fold_1 ls1 ls2 ls3 n with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  unfold side_find_arithseq_fold_1.
  destruct n; trivial.
  destruct_spec (side_find_arithseq_3_fold').
  1: apply arithseq_3_def_spec.
  destruct_spec (side_find_arithseq_S_fold); trivial.
  apply arithseq_S_def_spec.
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

Lemma side_find_arithseq_fold_2_spec ls1 ls2 ls3 n n0:
  match side_find_arithseq_fold_2 ls1 ls2 ls3 n n0 with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  gen ls2 ls3 n.
  induction n0; intros; cbn; trivial.
  destruct n as [|n].
  - cbn.
    destruct ls2; cbn; trivial.
    apply IHn0.
  - destruct_spec side_find_arithseq_fold_1_spec.
    1: tauto.
    destruct ls2; cbn; trivial.
    apply IHn0.
Qed.

Lemma side_find_repeat_O_fold_spec s:
  match side_find_repeat_O_fold s with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  destruct s; cbn; trivial.
  destruct a; cbn; trivial.
  - destruct n; trivial.
    destruct n; trivial.
    apply repeat_0_def_spec'.
  - destruct n; trivial.
    destruct n; trivial.
    apply arithseq_0_def_spec'.
Qed.

Lemma side_find_repeat_fold_dynlen_spec ls:
  match side_find_repeat_fold_dynlen ls with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  induction ls.
  1,2: cbn; trivial.
  cbn[side_find_repeat_fold_dynlen].
  destruct_spec side_find_repeat_O_fold_spec.
  1: tauto.
  destruct (side_find_repeat_fold_dynlen ls).
  - apply side_concat_rw_2_spec',IHls.
  - destruct_spec side_find_repeat_fold_2_spec.
    1: tauto.
    destruct_spec enable_arithseq; trivial.
    destruct_spec side_find_arithseq_fold_2_spec; tauto.
Qed.

Lemma side_find_repeat_fold_fixedlen_spec ls1 ls2 n:
  match side_find_repeat_fold_fixedlen ls1 ls2 n with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  gen ls2 n.
  induction ls1; intros.
  1,2: cbn; trivial.
  cbn[side_find_repeat_fold_fixedlen].
  destruct_spec side_find_repeat_O_fold_spec.
  1: tauto.
  destruct_spec (IHls1).
  - apply side_concat_rw_2_spec'. tauto.
  - destruct_spec side_find_repeat_fold_1_spec.
    1: tauto.
    destruct_spec enable_arithseq; trivial.
    destruct_spec is_seg_repeat; trivial.
    destruct_spec side_find_arithseq_fold_2_spec; tauto.
Qed.

Lemma side_find_repeat_fold_spec ls:
  match side_find_repeat_fold ls with
  | None => True
  | Some x => to_prop0' (fst x)
  end.
Proof.
  unfold side_find_repeat_fold.
  destruct_spec (fixed_block_size).
  - apply side_find_repeat_fold_fixedlen_spec.
  - apply side_find_repeat_fold_dynlen_spec.
Qed.

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
| side_concat ((seg_concat r0 r1) as a) r => Some (seg_concat_def a)
| side_concat (seg_repeat a (from_nat 0)) r => Some (repeat_0_def a)
| side_concat (seg_repeat a _) r => Some (repeat_S_def a)
| side_concat (seg_arithseq a (from_nat 0)) r => Some (arithseq_0_def a)
| side_concat (seg_arithseq a _) r =>
  let a' := map (fun '(x0,x1,x2) => (from_seg x0,x1,match x2 with from_nat c => c | _ => N0 end)) a in
  arithseq_S_def a'
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
    + apply seg_concat_def_spec.
    + destruct n.
      1: destruct n.
      all: try (apply repeat_S_def_spec).
      apply repeat_0_def_spec.
    + destruct n.
      1: destruct n.
      all: try (apply arithseq_S_def_spec).
      apply arithseq_0_def_spec.
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
    match try_ind cfg.(mnc) w1' w0_ u0 with
    | Some (u1',u0') =>
      match follow_rule w1_ u1' with
      | None => reset_hlin_layers u0'
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
  pose proof (try_ind_spec cfg.(mnc) w1' w0_ u0).
  destruct (try_ind cfg.(mnc) w1' w0_ u0) as [[u1' u0']|].
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

Definition rep_rw_limit:nat := 16.

Fixpoint rep_rw(n:nat)(f:prop_expr'->option prop_expr')(x:prop_expr'*prop_expr'):prop_expr'*prop_expr' :=
match n with
| O => x
| Datatypes.S n0 =>
  let '(w1,w0):=x in
  match f w0 with
  | None => x
  | Some dw =>
    match follow_rule w0 dw with
    | None => x
    | Some w0 =>
      match follow_rule w1 dw with
      | None => x
      | Some w1 =>
        rep_rw n0 f (w1,w0)
      end
    end
  end
end.

Lemma rep_rw_spec n f (w:prop_expr'*prop_expr'):
(forall x,
to_prop' (fst x) ->
match f x with
| None => True
| Some x =>
  to_prop' (fst x)
end) ->
(let (w1,w0):=w in
to_prop' (fst w1) /\
to_prop' (fst w0)) ->
let (w1',w0'):=rep_rw n f w in
to_prop' (fst w1') /\
to_prop' (fst w0').
Proof.
  intros Hf.
  destruct w as [w1 w0].
  cbn.
  gen w1 w0.
  induction n; intros w1 w0 [H1 H0]; cbn.
  1: tauto.
  specialize (Hf w0).
  destruct (f w0) as [dw|]; cbn.
  2: tauto.
  destruct_spec follow_rule_spec'. 2: tauto.
  destruct_spec follow_rule_spec'. 2: tauto.
  apply IHn; tauto.
Qed.


Definition unfold_step1_fold w0 :=
let w := (step0_refl' w0,w0) in
let w := rep_rw rep_rw_limit find_repeat_unfold w in
let w := rep_rw rep_rw_limit find_step1 w in
let w := rep_rw rep_rw_limit find_repeat_fold w in
w.

Lemma unfold_step1_fold_spec w0:
to_prop' (fst w0) ->
let (w1,w0):=unfold_step1_fold w0 in
to_prop' (fst w1) /\
to_prop' (fst w0).
Proof.
  intros H.
  unfold unfold_step1_fold.
  repeat apply rep_rw_spec.
  - apply find_repeat_fold_spec.
  - apply find_step1_spec.
  - apply find_repeat_unfold_spec.
  - split.
    + apply step0_refl'_spec,H.
    + apply H.
Qed.

Definition step1_to_repeater_edge w0 :=
match find_repeat_unfold w0 with
| None => Some (fst (unfold_step1_fold w0))
| _ => None
end.

Definition steps_to_repeater_edge w0 :=
let w := unfold_step1_fold w0 in
let w := rep_rw rep_rw_limit step1_to_repeater_edge w in
w.

Lemma steps_to_repeater_edge_spec w0:
to_prop' (fst w0) ->
let (w1,w0):=steps_to_repeater_edge w0 in
to_prop' (fst w1) /\
to_prop' (fst w0).
Proof.
  intros H.
  unfold steps_to_repeater_edge.
  apply rep_rw_spec.
  - intros x Hx.
    unfold step1_to_repeater_edge.
    destruct (find_repeat_unfold x); trivial.
    pose proof (unfold_step1_fold_spec x).
    destruct (unfold_step1_fold x); cbn; tauto.
  - apply unfold_step1_fold_spec,H.
Qed.

Definition DH_config:Type := (list Sym)*(list Sym)*Q*dir.
Definition DH_step(x:DH_config):DH_config :=
let '(l,r,s,sgn):=x in
match tm (s,hd s0 r) with
| None => x
| Some (o,sgn',s') =>
  match sgn,sgn' with
  | L,L | R,R => (o::l,tl r,s',sgn')
  | _,_ => (o::(tl r),l,s',sgn')
  end
end.
Definition DH_steps(x:DH_config)(n:N):DH_config :=
N.iter n DH_step x.

Definition DH_config_to_config(x:DH_config):Q*tape :=
let '(l,r,s,sgn):=x in
let l' := l *> const s0 in
let m := hd s0 r in
let r' := (tl r) *> const s0 in
match sgn with
| L => (s,(r',m,l'))
| R => (s,(l',m,r'))
end.

Lemma DH_step_spec x:
  DH_config_to_config x
  -[tm]->*
  DH_config_to_config (DH_step x).
Proof.
  destruct x as [[[l r] s] sgn].
  cbn.
  destruct (tm (s,hd s0 r)) as [[[o sgn'] s']|] eqn:E.
  2: constructor.
  destruct sgn,sgn'; cbn;
  apply progress_evstep,progress_base.
  - destruct r as [|m [|m0 r]]; cbn; cbn in E;
    constructor; apply E.
  - destruct l,r; cbn; cbn in E;
    constructor; apply E.
  - destruct l,r; cbn; cbn in E;
    constructor; apply E.
  - destruct r as [|m [|m0 r]]; cbn; cbn in E;
    constructor; apply E.
Qed.

Lemma DH_steps_spec x n:
  DH_config_to_config x
  -[tm]->*
  DH_config_to_config (DH_steps x n).
Proof.
  induction n using N.peano_ind.
  - constructor.
  - eapply evstep_trans.
    1: apply IHn.
    eapply evstep_trans.
    1: apply DH_step_spec.
    applys_eq evstep_refl.
    f_equal.
    apply N.iter_succ.
Qed.

Definition DH_steps_from_init n :=
  DH_steps ([],[],q0,R) n.

Lemma DH_steps_from_init_spec n:
  c0
  -[tm]->*
  DH_config_to_config (DH_steps_from_init n).
Proof.
  applys_eq DH_steps_spec.
  reflexivity.
Qed.


Definition DH_side_to_expr(x:list Sym):side_expr :=
side_concat_list_seg (map seg_sym x) side_0inf.

Definition DH_config_to_expr(x:DH_config):config_expr :=
let '(l,r,s,sgn):=x in
(DH_side_to_expr l,DH_side_to_expr r,s,sgn).

Lemma DH_side_to_expr_spec l mp mpi:
  to_side mp mpi (DH_side_to_expr l) = l *> const s0.
Proof.
  induction l.
  1: reflexivity.
  cbn.
  rewrite <-IHl.
  reflexivity.
Qed.

Lemma DH_config_to_expr_spec x mp mpi:
  to_config mp mpi (DH_config_to_expr x) =
  DH_config_to_config x.
Proof.
  destruct x as [[[l r] s] sgn].
  cbn.
  destruct sgn.
  - f_equal.
    1: f_equal.
    1: f_equal.
    + rewrite DH_side_to_expr_spec.
      destruct r; reflexivity.
    + destruct r; reflexivity.
    + apply DH_side_to_expr_spec.
  - f_equal.
    1: f_equal.
    1: f_equal.
    + apply DH_side_to_expr_spec.
    + destruct r; reflexivity.
    + rewrite DH_side_to_expr_spec.
      destruct r; reflexivity.
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

Lemma N_iter_until_spec{S S'}{f:S->S+S'}{x:S+S'}{T:N}(P:S->Prop)(P':S'->Prop):
(forall x0:S, P x0 ->
match f x0 with
| inl x1 => P x1
| inr x1 => P' x1
end) ->
(match x with
| inl x1 => P x1
| inr x1 => P' x1
end) ->
match N_iter_until f x T with
| inl x1 => P x1
| inr x1 => P' x1
end.
Proof.
  intros H.
  destruct T as [|T].
  1: cbn; tauto.
  cbn.
  gen x.
  induction T; intros x Hx; cbn.
  - destruct x.
    + apply IHT,IHT,H,Hx.
    + apply Hx.
  - destruct x.
    + apply IHT,IHT,Hx.
    + apply Hx.
  - destruct x.
    + apply H,Hx.
    + apply Hx.
Qed.

Definition steps_to_repeater_edge' w :=
if (snd w =? 1)%positive then
  Some (fst (steps_to_repeater_edge w))
else None.

Lemma steps_to_repeater_edge'_spec x:
to_prop' (fst x) ->
match steps_to_repeater_edge' x with
| Some x0 => to_prop' (fst x0)
| None => True
end.
Proof.
  intro H.
  unfold steps_to_repeater_edge'.
  destruct (snd x =? 1)%positive; trivial.
  pose proof (steps_to_repeater_edge_spec x).
  destruct (steps_to_repeater_edge); cbn; tauto.
Qed.

Definition hlin_layers_step(s:(list hlin_layer)*bool):(list hlin_layer)*bool+(list hlin_layer) :=
let (ls,o):=s in
  match hlin_layers_upd' ls steps_to_repeater_edge' with
  | None => inr ls
  | Some ls =>
    inl (ls,false)
  end.

(*
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
*)
Definition initial_steps_prop:prop_expr' :=
  let s := DH_config_to_expr (DH_steps_from_init cfg.(initial_steps)) in
  ([],[multistep'_expr (side_0inf,side_0inf,q0,R) s false],1%positive).

Lemma initial_steps_prop_spec:
  to_prop' (fst initial_steps_prop).
Proof.
  intros mpi mp.
  cbn.
  unfold to_prop0_list; cbn.
  repeat rewrite Forall_cons_iff.
  repeat rewrite Forall_nil_iff.
  cbn.
  intro; split; trivial.
  applys_eq (DH_steps_from_init_spec).
  apply DH_config_to_expr_spec.
Qed.

Definition hlin_layers_steps T :=
N_iter_until hlin_layers_step (inl (reset_hlin_layers initial_steps_prop,true)) T.

Lemma hlin_layers_steps_spec T:
match hlin_layers_steps T with
| inl x => hlin_layers_WF (fst x)
| inr x =>hlin_layers_WF x
end.
Proof.
  apply N_iter_until_spec.
  - intros x Hx.
    unfold hlin_layers_step.
    destruct x as [ls o].
    cbn in Hx.
    destruct_spec hlin_layers_upd'_spec; cbn; auto.
    apply H; auto.
    apply steps_to_repeater_edge'_spec.
  - cbn.
    apply reset_hlin_layers_spec.
    apply initial_steps_prop_spec.
Qed.

Definition check_nonhalt(x:prop_expr):bool :=
match x with
| ([],[multistep_lb_expr s1 s2 (nat_var v1)]) => config_expr_eqb s1 (side_0inf,side_0inf,q0,R)
| _ => false
end.


Definition subst_for_nonhalt(n:N)(i:id_t)(t:type_t):to_type t :=
match t with
| nat_t => n
| seg_t => []
| side_t => const s0
end.

Lemma check_nonhalt_spec x:
  to_prop' x ->
  if check_nonhalt x then ~halts tm c0 else True.
Proof.
  intro H'.
  destruct x as [H G]; cbn.
  destruct H; trivial.
  destruct G as [|G G0]; trivial.
  destruct G; trivial.
  destruct n; trivial.
  destruct G0; trivial.
  destruct (config_expr_eqb_spec a (side_0inf, side_0inf, q0, R)); trivial.
  subst a.
  apply multistep_lb_nonhalt.
  intro n.
  specialize (H' N0 (subst_for_nonhalt (N.of_nat n))).
  unfold to_prop'' in H'.
  cbn in H'.
  unfold to_prop0_list in H'.
  repeat rewrite Forall_cons_iff in H'.
  repeat rewrite Forall_nil_iff in H'.
  cbn in H'.
  destruct (H' I) as [H0 _].
  eexists.
  applys_eq H0.
  lia.
Qed.

Definition decide_hlin_nonhalt T :=
match hlin_layers_steps T with
| inr ((_,(w1,w0),_)::_) => check_nonhalt (fst w0)
| _ => false
end.

Lemma decide_hlin_nonhalt_spec' T:
  if decide_hlin_nonhalt T then ~halts tm c0 else True.
Proof.
  unfold decide_hlin_nonhalt.
  destruct_spec hlin_layers_steps_spec; trivial.
  destruct l as [|[[[w3 w2] [w1 w0]] p] ls]; trivial.
  unfold hlin_layers_WF in H.
  rewrite Forall_cons_iff in H.
  cbn in H.
  destruct_spec check_nonhalt_spec; trivial.
  tauto.
Qed.
Lemma decide_hlin_nonhalt_spec T:
  decide_hlin_nonhalt T = true -> ~halts tm c0.
Proof.
  pose proof (decide_hlin_nonhalt_spec' T) as H.
  intro H0.
  rewrite H0 in H.
  apply H.
Qed.

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





