(* Counter class 4, TM1/TM2 in REST3_20261013.txt (global entries 7/8).
   Shared finite digit recursion, with the two original machines below.
   No simulation certificate or affine-permutation analysis is needed. *)
From BusyCoq Require Import Individual62 ES_v3.
Require Import String List Bool Arith Lia ZifyNat.
Import ListNotations.

Module Counter.
Close Scope sym.

(* Digits are low first. T is the affine permutation of the informal proof,
   expressed relationally to avoid division, bit indices and large integers. *)
Inductive T : list bool -> list bool -> Prop :=
| T_nil : T [] []
| T_snoc x y z e : T x y -> T y z -> T (x++[e]) (negb e::z).

Lemma T_length x y : T x y -> length x=length y.
Proof. intro H; induction H; cbn; rewrite ?length_app; cbn; lia. Qed.

Lemma T_total_bound n : forall x, length x<=n -> exists y, T x y.
Proof.
  induction n; intros x Hx; destruct x using rev_ind.
  - exists (@nil bool); constructor.
  - rewrite length_app in Hx; cbn in Hx; lia.
  - exists (@nil bool); constructor.
  - rewrite length_app in Hx; cbn in Hx.
    destruct (IHn x0 ltac:(lia)) as [y Hy].
    destruct (IHn y ltac:(pose proof (T_length _ _ Hy); lia)) as [z Hz].
    exists (negb x::z); econstructor; eassumption.
Qed.

Lemma T_total x : exists y, T x y.
Proof. apply (T_total_bound (length x)); lia. Qed.

(* cost = twice the width minus the number of 1 bits.
   00 ++ body x is the low-first 00/001 encoding followed by 00. *)
Definition bit (e:bool) : nat := if e then 1 else 0.
Fixpoint cost (x:list bool) : nat :=
  match x with [] => 0 | e::x => (2-bit e)+cost x end.
Fixpoint body (x:list bool) : list Sym :=
  match x with [] => [] | e::x => [S1]^^(bit e)++[S0;S0]++body x end.

Lemma cost_app x y : cost (x++y)=cost x+cost y.
Proof. induction x; cbn[cost app]; [reflexivity|rewrite IHx; lia]. Qed.
Lemma body_app x y : body (x++y)=body x++body y.
Proof. induction x; [reflexivity|destruct a; cbn[body bit lpow app]; now rewrite IHx]. Qed.

End Counter.

Module MachineRules.
Close Scope sym.
Notation U n := ([S1]^^n).
(* The left stack stores run lengths nearest first, unlike the displayed
   bracket notation in the informal proof. Every run has a preceding zero. *)
Fixpoint left (xs:list nat) l : side :=
  match xs with [] => l | a::xs => left xs l <* [S0] <* U a end.
Definition cfg (q:Q) l xs r := left xs l {{q}}> S0>>r.

Record Rules (tm:TM) (q:Q) : Prop := {
  ruleP : forall a b k l r,
    cfg q l [2+b;2+a] (U k*>[S0]*>r) -[tm]->*
    cfg q l [2+k;1+b;1+a] r;
  ruleM : forall a b l r,
    cfg q l [1+b;1;1+a] r -[tm]->*
    cfg q l [3+a] (U b*>[S0;S0]*>r)
}.

Section RulesProof.
Context {tm:TM} {q:Q} (rules:Rules tm q).

Lemma P xs a b k l r : 2<=a -> 2<=b ->
  cfg q l (b::a::xs) (U k*>[S0]*>r) -[tm]->*
  cfg q l ((2+k)::(b-1)::(a-1)::xs) r.
Proof.
  intros; applys_eq (ruleP _ _ rules (a-2) (b-2) k (left xs l) r);
    unfold cfg; cbn[left]; flia.
Qed.

Lemma M xs a b l r : 1<=a -> 1<=b ->
  cfg q l (b::1::a::xs) r -[tm]->*
  cfg q l ((a+2)::xs) (U (b-1)*>[S0;S0]*>r).
Proof.
  intros; applys_eq (ruleM _ _ rules (a-1) (b-1) (left xs l) r);
    unfold cfg; cbn[left]; flia.
Qed.

Ltac p :=
  lazymatch goal with
  | |- cfg _ _ _ ([S1]^^?kk *> _) -[_]->* _ =>
    eapply evstep_trans; [apply P with (k:=kk); lia|]
  | |- _ => eapply evstep_trans; [apply P with (k:=0%nat); lia|]
  end.
Ltac m := eapply evstep_trans; [apply M; lia|].
Ltac done := apply evstep_refl'; flia.

Lemma G xs a b g l r :
  cfg q l ((3+b)::(3+a)::xs) ([S0]*>U g*>[S0;S0]*>r) -[tm]->*
  cfg q l ((3+g)::(2+b)::(1+a)::xs) ([S0;S0]*>r).
Proof. p; p; m; p; done. Qed.

Lemma J xs a b g l r :
  cfg q l ((4+b)::(3+a)::xs) ([S0;S0]*>U g*>[S0;S0]*>r) -[tm]->*
  cfg q l ((3+b)::(1+a)::xs) (U (2+g)*>[S0;S0;S1;S0;S0]*>r).
Proof. p; p; m; p; p; p; m; p; p; p; m; m; done. Qed.

Lemma K xs a x y l r :
  cfg q l (4::(3+a)::xs) ([S0]*>U (1+x)*>[S0;S0]*>U (1+y)*>[S0;S0]*>r) -[tm]->*
  cfg q l ((3+a)::xs) (U (2+x)*>[S0;S0]*>U (3+y)*>[S0;S0;S1;S0;S0]*>r).
Proof. p; p; m; p; p; p; m; p; p; p; m; p; p; p; m; m; m; done. Qed.

(* Generalizing the remaining left counter b makes the digit induction
   compositional: the two premises of T_snoc are exactly the two calls. *)
Definition Kernel n c d v u := forall xs a b g l r, 1<=a -> 3<=b ->
  cfg q l ((b+1+n*2)::(a+2+c)::xs) ([S0;S0]*>v*>U g*>[S0;S0]*>r) -[tm]->*
  cfg q l (b::a::xs) (U (2+d+g)*>[S0;S0]*>U (1+n*2)*>[S0;S0]*>u*>r).

Lemma L0 n c d v u (I:Kernel n c d v u) xs a b g l r :
  cfg q l ((5+b)::(3+a)::xs)
    (U (2+c)*>[S0;S0]*>U (1+n*2)*>[S0;S0]*>v*>U g*>[S0;S0]*>r) -[tm]->*
  cfg q l ((3+b)::(1+a)::xs)
    (U (3+d+g)*>[S0;S0]*>U (3+n*2)*>[S0;S0;S1;S0;S0]*>u*>r).
Proof.
  p; p; p; m; p.
  eapply evstep_trans; [applys_eq (I ((2+b)::(2+a)::xs) 1 3 g l r); flia|].
  m; p; p; p; m; p; p; p; m; p; p; p; m; p; p; p; m; m; m; done.
Qed.

Lemma L1 n c d v u (I:Kernel n c d v u) xs a b g l r :
  cfg q l ((5+b)::(2+a)::xs)
    (U (3+c)*>[S0;S0]*>U (1+n*2)*>[S0;S0]*>v*>U g*>[S0;S0]*>r) -[tm]->*
  cfg q l ((3+b)::(1+a)::xs)
    (U (4+d+g)*>[S0;S0]*>U (3+n*2)*>[S0;S0;S0;S0]*>u*>r).
Proof.
  p; p; p; m; p.
  eapply evstep_trans; [applys_eq (I ((2+b)::(1+a)::xs) 2 3 g l r); flia|].
  p; p; p; m; m; p; p; p; m; m; done.
Qed.

Lemma T_spec x y : Counter.T x y ->
  Kernel (length x) (Counter.cost x) (Counter.cost y) (Counter.body x) (Counter.body y).
Proof.
  intro H; induction H; unfold Kernel in *; intros xs a b g l r Ha Hb.
  - cbn[Counter.cost Counter.body length].
    applys_eq (J xs (a-1) (b-3) g l r); flia.
  - pose proof (Counter.T_length _ _ H) as Hl.
    rewrite length_app, Counter.cost_app, Counter.body_app.
    destruct e; cbn[Counter.cost Counter.body Counter.bit negb length lpow app].
    + eapply evstep_trans.
      * applys_eq (IHT1 xs (a+1) (b+2) 1 l (U g*>[S0;S0]*>r)); try lia.
        repeat rewrite Str_app_assoc; flia.
      * applys_eq (L1 (length y) (Counter.cost y) (Counter.cost z)
          (Counter.body y) (Counter.body z) IHT2 xs (a-1) (b-3) g l r); flia.
    + eapply evstep_trans.
      * applys_eq (IHT1 xs (a+2) (b+2) 0 l (U g*>[S0;S0]*>r)); try lia.
        repeat rewrite Str_app_assoc; flia.
      * applys_eq (L0 (length y) (Counter.cost y) (Counter.cost z)
          (Counter.body y) (Counter.body z) IHT2 xs (a-1) (b-3) g l r); flia.
Qed.

End RulesProof.

Definition edge (f:Q) k r := (const S0) {{f}}> [S0;S0]*>U (2+k)*>[S0;S0]*>r.
Definition root f k n r := edge f k (U n*>[S0;S0]*>r).
Definition state f k x := root f k (2+Counter.cost x)
  (U (1+length x*2)*>[S0;S0]*>Counter.body x*>(const S0)).

Record Boundary (tm:TM) (q f:Q) k : Prop := {
  entry : forall n r, root f k n r -[tm]->+
    cfg q (const S0) [2+n;3+k] ([S0]*>r);
  exit : forall r, cfg q (const S0) [3+k] r -[tm]->* edge f k r
}.

(* Two left-edge returns implement x -> true::T(x), for every bit list. *)
Lemma round tm q f k (rules:Rules tm q) (bound:Boundary tm q f k) x y :
  Counter.T x y -> state f k x -[tm]->+ state f k (true::y).
Proof.
  intro H; pose proof (Counter.T_length _ _ H) as Hl.
  unfold state at 1.
  follow10 (entry _ _ _ _ bound).
  eapply evstep_trans.
  - applys_eq (G rules [] k (1+Counter.cost x) (1+length x*2)
      (const S0) (Counter.body x*>(const S0))); flia.
  - eapply evstep_trans.
    + applys_eq (T_spec rules _ _ H [1+k] 1 3 0 (const S0) (const S0));
        try lia; flia; try solve_const0_eq.
    + eapply evstep_trans; [apply (M rules); lia|].
      replace (1+k+2) with (3+k) by lia.
      follow (exit _ _ _ _ bound).
      fold (root f k 2).
      follow100 (entry _ _ _ _ bound).
      eapply evstep_trans.
      * applys_eq (K rules [] k (1+Counter.cost y) (length x*2)
          (const S0) (Counter.body y*>(const S0))); flia.
      * follow (exit _ _ _ _ bound).
        unfold state, root, edge; cbn[Counter.cost Counter.body Counter.bit length].
        apply evstep_refl'; flia.
Qed.

Lemma nonhalt tm q f k (rules:Rules tm q) (bound:Boundary tm q f k) x :
  ~halts tm (state f k x).
Proof.
  apply (progress_nonhalt_simple tm _ (state f k) x).
  intro v; destruct (Counter.T_total v) as [w H].
  exists (true::w); eapply round; eassumption.
Qed.

End MachineRules.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LA_1LC0RA_0LD1RC_---0LE_0LF1LE_1RF1LB").

Lemma rules : MachineRules.Rules tm C.
Proof.
  constructor; intros; unfold MachineRules.cfg; cbn[MachineRules.left].
  - es' a b k & l r.
  - es' a b & l r.
Qed.

Lemma boundary : MachineRules.Boundary tm C F 0.
Proof.
  constructor; intros; unfold MachineRules.root, MachineRules.edge, MachineRules.cfg;
    cbn[MachineRules.left].
  - es' n & r.
  - es' & r.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=MachineRules.state F 0 [true;false]).
  - unfold MachineRules.state, MachineRules.root, MachineRules.edge; esx.
  - eapply MachineRules.nonhalt; [apply rules|apply boundary].
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC1LB_1LD0RB_0LE1RD_---0LF_0LA1LF").

Lemma rules : MachineRules.Rules tm D.
Proof.
  constructor; intros; unfold MachineRules.cfg; cbn[MachineRules.left].
  - es' a b k & l r.
  - es' a b & l r.
Qed.

Lemma boundary : MachineRules.Boundary tm D A 1.
Proof.
  constructor; intros; unfold MachineRules.root, MachineRules.edge, MachineRules.cfg;
    cbn[MachineRules.left].
  - es' n & r.
  - es' & r.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=MachineRules.state A 1 [true;false]).
  - unfold MachineRules.state, MachineRules.root, MachineRules.edge; esx.
  - eapply MachineRules.nonhalt; [apply rules|apply boundary].
Qed.
End TM2.
