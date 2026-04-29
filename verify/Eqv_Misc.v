From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import ZArith.
Require Import String.
From BusyCoq Require Import DivModCases.

Module TM1.
Definition tm := TM_from_str "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---1RC".
Definition tm' := TM_from_str "1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC".

Inductive LD := D11 | D10 | D1.

Inductive Config :=
| cfg1(l:list LD)(c' b:nat)
| cfg2(l:list LD)(c' b c:nat)
| cfg3(c' a b:nat)
.

Notation "l <| r" := (l <{{B}} 0>>r) (at level 30).

Section to_config_sec.
Hypothesis s:sym.
Definition w := <[1;s;1;s;1].

Fixpoint LC ls c :=
match ls with
| [] => 0inf <* w^^c <* <[0;0]
| D11::t => LC t c <* <[1;s]
| D10::t => LC t c <* <[1;0]
| D1::t => LC t c <* <[1]
end.

Definition to_config x :=
match x with
| cfg1 l c b => LC l c <* <[0;0] <* <[1;0]^^b {{A}}> 0inf
| cfg2 l c' b c => LC (D1::l) c' <* <[0] <* <[0;1]^^b {{D}}> [0] *> [1]^^c *> 0inf
| cfg3 c' a b => 0inf <* w^^c' <* <[0;0] <| [1]^^(2+a) *> [0] *> [1]^^b *> 0inf
end.

Fixpoint sum ls :=
match ls with
| [] => O
| D11::t => (sum t)+2
| D10::t => (sum t)+2
| D1::t => (sum t)+1
end.

Lemma LC_ws n:
  LC ([D1;D11;D11]^^n) 0 = 0inf <* w^^n.
Proof.
  induction n; cbn.
  1: solve_const0_eq.
  congruence.
Qed.

Lemma LC_D10s n m:
  LC ([D10]^^n) m = 0inf <* w^^m <* <[0;0] <* <[1;0]^^n.
Proof.
  induction n; cbn.
  1: trivial.
  rewrite IHn; trivial.
Qed.

End to_config_sec.

Lemma LL l r c:
  LC 0 l c <| r -[ tm' ]->*
  0inf <* (w 0)^^c <* <[0;0] <| [1]^^(sum l) *> r.
Proof.
  gen r.
  induction l as [|[] t]; cbn; intros.
  all: es; er; follow; es.
Qed.

Lemma LL' l r c:
  LC 1 l c <| r -[ tm ]->*
  0inf <* (w 1)^^c <* <[0;0] <| [1]^^(sum l) *> r.
Proof.
  gen r.
  induction l as [|[] t]; cbn; intros.
  all: es; er; follow; es.
Qed.

Definition f x :=
(match x with
| cfg1 l c b =>
  match b with
  | 0 => Some (cfg3 c ((sum l)+4) 0)
  | S b => Some (cfg1 (D1::D11::D11::l) c b)
  end
| cfg2 l c' b c =>
  match b with
  | 0 => Some (cfg3 c' ((sum l)+c) 0)
  | 1 => Some (cfg3 c' ((sum l)) (1+c))
  | 2 =>
    match c with
    | 0 => None
    | 1 => Some (cfg3 c' ((sum l)+7) 0)
    | S (S c) =>
      match mod2 c with
      | mod2eq0 c => Some (cfg2 (D11::D11::D11::D1::l) c' c 0)
      | mod2eq1 c => Some (cfg1 (D1::D11::D11::D11::D1::l) c' c)
      end
    end
  | S (S (S b)) => Some (cfg2 (D11::D11::D1::l) c' b (1+c))
  end
| cfg3 c a b =>
  match a with
  | 0 =>
    match mod2 b with
    | mod2eq0 b => Some (cfg2 (D11::D11::[D1;D11;D11]^^c) 0 b 0)
    | mod2eq1 b => Some (cfg1 ([D1;D11;D11]^^(1+c)) 0 b)
    end
  | S a =>
    match mod2 a with
    | mod2eq0 a => Some (cfg2 (D11::D11::[D1;D11;D11]^^c) 0 a b)
    | mod2eq1 a =>
      match b with
      | 0 => Some (cfg1 ([D1;D11;D11]^^(1+c)) 0 a)
      | S b =>
        match mod2 b with
        | mod2eq0 b => Some (cfg2 ([D10]^^a) (1+c) (b) 0)
        | mod2eq1 b => Some (cfg1 (D1::[D10]^^a) (1+c) b)
        end
      end
    end
  end
end)%nat.

Definition cfg0 := cfg3 0 0 0.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | mod2eq0 _ => _ | _ => _ end] =>
  destruct a; subst
end.

Ltac solve_v1 s :=
  erewrite <-(halts_iff _ _ _ f (to_config s) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config,w in *;
  repeat des_nat;
  try (split; trivial);
  cbn;
  repeat (rewrite LC_ws || rewrite LC_D10s);
  try solve[esx; er; follow; es].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  pose proof LL'.
  solve_v1 1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  pose proof LL.
  solve_v1 0.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM1.


Module TM2.
Definition tm := TM_from_str "1LB1LD_0RC1LA_1LA1RC_1LA1RE_1LF0RD_---0LE".
Definition tm' := TM_from_str "1LB1LD_0RC1LA_1LA1RC_0LB1RE_1LF0RD_---0LE".

Definition to_config '(a,b,c) := 0inf <* [1]^^(a) <{{D}} [1;1]^^(b) *> [1;0]^^(c) *> 0inf.
Definition cfg0 := (0,1,0)%nat.

Definition f '(a,b,c) :=
(match a with
| 0 =>
  match c with
  | 0 => Some (1+b*2,1,0)
  | 1 => Some (2+b*2,1,0)
  | S (S c) => Some (2+b*2,1,1+c)
  end
| 1 =>
  match c with
  | 0 => None
  | 1 => Some (3+b*2,1,0)
  | S (S c) => Some (4+b*2,1,c)
  end
| 2 =>
  match c with
  | 0 => Some (2,1,b)
  | S c => Some (0,2+b,c)
  end
| 3 =>
  match c with
  | 0 => Some (4,1,b)
  | S c => Some (1,2+b,c)
  end
| S (S (S (S a))) =>
  match c with
  | 0 => Some (a,2,1+b)
  | S c => Some (2+a,2+b,c)
  end
end)%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 :=
  erewrite <-(halts_iff _ _ _ f to_config (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [[a b] c] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM2.


Module TM3.
Definition tm := TM_from_str "1RB1RA_0RC1RF_1LD---_0LE1LE_1RA1LD_1LD0LF".
Definition tm' := TM_from_str "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC".

Definition to_config '(a,b,c) := 0inf <{{E}} [1;1]^^(2+a) *> [0]^^(1+b*2) *> [1]^^c *> [0;1] *> 0inf.

Definition f '(a,b,c) :=
(match b with
| O =>
  match c with
  | O => None
  | S O => Some (0,1,9+a*2)
  | S (S c) => Some (0,3+a,c)
  end
| S O =>
  match c with
  | O => Some (0,1,11+a*2)
  | S c => Some (0,4+a,c)
  end
| S (S b) => Some (3+a,b,c)
end)%nat.

Definition cfg0 := (0,1,5)%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 :=
  erewrite <-(halts_iff _ _ _ f to_config (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [[a b] c] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM3.


Module TM4.
Definition tm := TM_from_str "1LB1RE_1LC1LA_0RD1LB_1RB1RD_1LF0RA_---0LE".
Definition tm' := TM_from_str "1LB1LD_0RC1LA_1RA1RC_1LA1RE_1LF0RD_---0LE".

Definition to_config (q:Q) '(a,b,c) := 0inf <* [1]^^(a) <{{ q }} [1;1]^^(b) *> [1;0]^^(c) *> 0inf.
Definition cfg0 := (0,250,5)%nat.

Definition f '(a,b,c) :=
(match a with
| 0 =>
  match c with
  | 0 => Some (1+b*2,1,1)
  | 1 => Some (2+b*2,1,1)
  | S (S c) => Some (4+b*2,0,1+c)
  end
| 1 =>
  match c with
  | 0 => None
  | 1 => Some (3+b*2,1,1)
  | 2 => Some (4+b*2,1,1)
  | S (S (S c)) => Some (6+b*2,0,1+c)
  end
| 2 =>
  match c with
  | 0 =>
    match b with
    | 0 => Some (2,1,1)
    | S b => Some (4,0,1+b)
    end
  | S c => Some (0,2+b,c)
  end
| 3 =>
  match c with
  | 0 =>
    match b with
    | 0 => Some (4,1,1)
    | S b => Some (6,0,1+b)
    end
  | S c => Some (1,2+b,c)
  end
| S (S (S (S a))) =>
  match c with
  | 0 => Some (a,2,1+b)
  | S c => Some (2+a,2+b,c)
  end
end)%nat.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 q :=
  erewrite <-(halts_iff _ _ _ f (to_config q) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; shelve | ];
  intros [[a b] c] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  solve[esx].

Ltac stepn n0 :=
  eapply without_counter with (n:=N.to_nat n0);
  eapply multistep_c_spec; vm_compute; simpl_tape; try reflexivity.

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A.
  Unshelve.
  stepn 2002118%N.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D.
  Unshelve.
  stepn 2095634%N.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM4.


Module TM5.
Definition tm := TM_from_str "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1RA1RE_---0LD".
Definition tm' := TM_from_str "1LB0RC_1RC0LE_1RD1RC_1RA1LD_1LF1LB_---0LB".

Close Scope sym.

Definition f0 (tp:bool) (l:list nat) (a b m:nat) (r:list nat) :=
if tp then
match m with
| S m => Some (true,l<:(1+a)<:(1+b),m,r)
| O =>
  match r with
  | c::r => Some (true,l<:a<:(2+b)<:0,c,r)
  | [] =>
    match mod2 b with
    | mod2eq0 b => Some (true,l<:(2+a),1+b,[])
    | mod2eq1 b => Some (false,l<:a,2+b,[])
    end
  end
end
else
match b with
| O => None
| S O => Some (true,l<:(1+a),1+m,r)
| S (S b) =>
  match mod2 b with
  | mod2eq0 b => Some (false,l<:a,b,m::r)
  | mod2eq1 b => Some (true,l<:(2+a),b,m::r)
  end
end.

Definition f '(tp,l,m,r) :=
match l with
| [] => f0 tp [] 0 0 m r
| [b] => f0 tp [] 0 b m r
| b::a::l => f0 tp l a b m r
end.

Definition cfg0 := (true,[2],0,@nil nat).

Open Scope sym.

Section to_config_sec.
Hypothesis QR:Q.
Hypothesis w:list sym.

Fixpoint LC ls :=
match ls with
| [] => 0inf
| n::ls => LC ls <* [0] <* [1]^^n
end.

Fixpoint RC ls :=
match ls with
| [] => w *> 0inf
| n::ls => [0] *> [0;1]^^(1+n) *> RC ls
end.

Definition to_config '(tp,l,m,r) :=
match tp with
| true => LC l {{QR}}> [0;1]^^m *> RC r
| false => LC l <{{F}} [1] *> [0;1]^^m *> RC r
end.

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match mod2 ?a with _ => _ end] =>
  destruct (mod2 a); subst
end.

Ltac solve_v1 a' b' :=
  erewrite <-(halts_iff _ _ _ f (to_config a' b') (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [[[[] [|b [|a l]]] m] r] _;
  unfold f,f0,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[LC RC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E [1].
  - replace a with O in * by lia.
    es.
  - lia.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C (@nil sym).
  - replace a with O in * by lia.
    es.
  - lia.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM5.


Module TM6.
Definition tm := TM_from_str "1RB0LB_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF".
Definition tm' := TM_from_str "1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF".

Fixpoint LC ls :=
match ls with
| [] => 0inf
| n::ls => LC ls <* [1]^^(1+n) <* [0]
end.

Inductive Config :=
| S1 (l:list nat)(a b c:nat)(r:list nat)
| S2 (l:list nat)(a:nat)(r:list nat).

Definition to_config x :=
match x with
| S1 l a b c r =>
  LC l <* [1]^^(1+a) <* [0] <* [1]^^b <{{F}} [0;0;1] *> [1]^^c *> LC r
| S2 l a r =>
  LC l <* [1]^^(1+a) {{D}}> LC r
end.

Close Scope sym.

Definition f x :=
match x with
| S1 l a b c r =>
  match b with
  | O => Some (S2 (l<:a) (2+c) r)
  | S O =>
    match l with
    | l<:a0 => Some (S1 l a0 (1+a) 0 (c::r))
    | [] =>
      match a with
      | S a => Some (S1 [] 0 a 1 (c::r))
      | O => None
      end
    end
  | S (S b) => Some (S1 l (1+a) b (1+c) r)
  end
| S2 l a r =>
  match r with
  | c::r => Some (S2 (l<:a) c r)
  | [] =>
    match l with
    | l<:a0 => Some (S1 l a0 a 0 [])
    | [] =>
      match a with
      | S (S a) => Some (S1 [] 0 a 1 [])
      | _ => None
      end
    end
  end
end.

Definition cfg0 := S2 [] 2 [].

Open Scope sym.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 :=
  erewrite <-(halts_iff _ _ _ f (to_config) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[LC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM6.


Module TM7.
Definition tm := TM_from_str "1RB1RA_1RC1LB_1LD0RA_1RA0LE_---0LF_0RD0LB".
Definition tm' := TM_from_str "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB".

Fixpoint LC ls :=
match ls with
| [] => 0inf
| n::ls => LC ls <* [1]^^(1+n) <* [0]
end.

Fixpoint RC ls :=
match ls with
| [] => 0inf
| n::ls => RC ls <* [1]^^(1+n) <* [0;0]
end.

Inductive Config :=
| S1 (l:list nat)(a b c:nat)(r:list nat)
| S2 (l:list nat)(a:nat)(r:list nat).

Definition to_config x :=
match x with
| S1 l a b c r =>
  LC l <* [1]^^(1+a) <* [0] <* [1]^^b <{{B}} [0;0;0;1] *> [1]^^c *> RC r
| S2 l a r =>
  LC l <* [1]^^(a) {{A}}> RC r
end.

Close Scope sym.

Definition f x :=
match x with
| S1 l a b c r =>
  match b with
  | O =>
    match l with
    | l<:a0 =>
      match a with
      | S a => Some (S1 l a0 a 0 (c::r))
      | O => Some (S2 (l<:(1+a0)) 2 (c::r))
      end
    | [] =>
      match a with
      | 0 => Some (S2 [0] 2 (c::r))
      | 1 => None
      | 2 => Some (S2 [1] 3 (c::r))
      | S (S (S a)) => Some (S1 [] 0 a 1 (c::r))
      end
    end
  | S O => Some (S2 (l<:(2+a)) (3+c) r)
  | S (S b) => Some (S1 l (1+a) b (1+c) r)
  end
| S2 l a r =>
  match r with
  | c::r => Some (S2 (l<:(1+a)) c r)
  | [] =>
    match l with
    | l<:a0 =>
      match a with
      | O => Some (S1 l (1+a0) 1 0 [])
      | S a => Some (S1 l a0 a 0 [])
      end
    | [] =>
      match a with
      | 0 => Some (S1 [] 0 1 0 [])
      | 1 => None
      | 2 => Some (S2 [1] 3 [])
      | S (S (S a)) => Some (S1 [] 0 a 1 [])
      end
    end
  end
end.

Definition cfg0 := S2 [] 0 [].

Open Scope sym.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 :=
  erewrite <-(halts_iff _ _ _ f (to_config) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[LC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM7.


Module TM8.
Definition tm := TM_from_str "1LB0RB_0RC0LE_0LE0RD_1RA1LF_1LF---_1RC0LB".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1LB_1LF0RF_0RC0LA".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L011 | L0101 | L0100(n:nat)
.

Inductive Config :=
| hR(l:list LD)(n:nat)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QR1 QR2 QL:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L011::ls => toLC ls <* <[0;1;1]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L0100 n::ls => toLC ls <* <[0;1;0;0] <* <[1]^^n
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hR l n r =>
  match n with
  | 0%nat => toLC l <* <[0;1] {{QR1}}> r
  | 1%nat => toLC l <* <[0;1;0] {{QR2}}> r
  | 2%nat => toLC l <* <[0;1;0;0] {{C}}> r
  | S(S(S n)) => toLC l <* <[0;1;0;0] <* <[1]^^n <* <[0] {{D}}> r
  end
| hL l r => toLC l <{{QL}} [1;0] *> r
end.

Definition f x :=
match x with
| hR l 0 (0>>r) => Some (hL l (1>>r))
| hR l 0 (1>>r) => Some (hR l 1 r)
| hR l 1 (0>>r) => Some (hR l 2 r)
| hR l 1 (1>>r) => Some (hL l ([1;0]*>r))
| hR l 2 (0>>r) => Some (hR (l<:L011) 0 r)
| hR l 2 (1>>r) => Some (hR l 3 r)
| hR l (S(S(S n))) (0>>r) => Some (hR (l<:(L0100 n)) 0 r)
| hR l (S(S(S n))) (1>>r) => Some (hR l (S(S(S(S n)))) r)
| hL [] r => Some (hR [] 2 r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:(L0100 0)) r => Some (hR (l<:L0101) 0 r)
| hL (l<:(L0100 1)) r => Some (hR (l<:L011) 2 r)
| hL (l<:(L0100 2)) r => Some (hL l ([0;1;0;1;1;0]*>r))
| hL (l<:(L0100 _)) r => None
end.

Definition cfg0 := hR [] 0 ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 a' b' c' d' :=
  erewrite <-(halts_iff _ _ _ f (to_config a' b' c' d') (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E F B <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM8.


Module TM9.
Definition tm := TM_from_str "1LB---_1LC0RF_1RD0LF_0LB0RE_1RB1RA_0RD0LB".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_1LA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L011 | L0101 | L0100 | L01001
.

Inductive Config :=
| hR(l:list LD)(n:nat)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QR1 QR2 QR3 QR4 QR5 QL:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L011::ls => toLC ls <* <[0;1;1]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hR l n r =>
  match n with
  | 0%nat => toLC l <* <[0;1] {{QR1}}> r
  | 1%nat => toLC l <* <[0;1;0] {{QR2}}> r
  | 2%nat => toLC l <* <[0;1;0;0] {{QR3}}> r
  | 3%nat => toLC l <* <[0;1;0;0;0] {{QR4}}> r
  | _ => toLC l <* <[0;1;0;0;0;1] {{QR5}}> r
  end
| hL l r => toLC l <{{QL}} [1;0] *> r
end.

Definition f x :=
match x with
| hR l 0 (0>>r) => Some (hL l (1>>r))
| hR l 0 (1>>r) => Some (hR l 1 r)
| hR l 1 (0>>r) => Some (hR l 2 r)
| hR l 1 (1>>r) => Some (hL l ([1;0]*>r))
| hR l 2 (0>>r) => Some (hR (l<:L011) 0 r)
| hR l 2 (1>>r) => Some (hR l 3 r)
| hR l 3 (0>>r) => Some (hR (l<:L0100) 0 r)
| hR l 3 (1>>r) => Some (hR l 4 r)
| hR l _ (0>>r) => Some (hR (l<:L01001) 0 r)
| hR l _ (1>>r) => None
| hL [] r => Some (hR [] 2 r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L0100) r => Some (hR (l<:L0101) 0 r)
| hL (l<:L01001) r => Some (hR (l<:L011) 2 r)
end.

Definition cfg0 := hR [] 0 ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B F D E A C <[1;0;1;1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A E C D F B <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM9.


Module TM10.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L01000 | L01001
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h01000E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| h010C(l:list LD)(r:side)
| h0101E(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h01000E l r => toLC l <* <[0;1;0;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| h010C l r => toLC l <* <[0;1;0] {{QC}}> r
| h0101E l r => toLC l <* <[0;1;0;1] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h01000E l (0>>r) => Some (hL (l<:L0100) r)
| h01000E l (1>>r) => Some (h0A (l<:L01000) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h010C l r)
| h01F l (1>>r) => None
| h010C l (0>>r) => Some (h0101E l r)
| h010C l (1>>r) => Some (hL l (1>>0>>r))
| h0101E l (0>>r) => Some (h01000E l r)
| h0101E l (1>>r) => Some (h0A (l<:L0101) r)
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM10.


Module TM11.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L01000 | L01001
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h01000E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| h010C(l:list LD)(r:side)
| h0101E(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h01000E l r => toLC l <* <[0;1;0;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| h010C l r => toLC l <* <[0;1;0] {{QC}}> r
| h0101E l r => toLC l <* <[0;1;0;1] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h01000E l (0>>r) => Some (hL (l<:L0100) r)
| h01000E l (1>>r) => Some (h0A (l<:L01000) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h010C l r)
| h01F l (1>>r) => None
| h010C l (0>>r) => Some (h0101E l r)
| h010C l (1>>r) => Some (hL l (1>>0>>r))
| h0101E l (0>>r) => Some (h01000E l r)
| h0101E l (1>>r) => Some (h0A (l<:L0101) r)
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM11.


Module TM12.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1RB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L01000 | L01001 | L0111 | L01100 | L01101
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h011B(l:list LD)(r:side)
| h0110D(l:list LD)(r:side)
| h01100E(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| L01100::ls => toLC ls <* <[0;1;1;0;0]
| L01101::ls => toLC ls <* <[0;1;1;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011B l r => toLC l <* <[0;1;1] {{QB}}> r
| h0110D l r => toLC l <* <[0;1;1;0] {{QD}}> r
| h01100E l r => toLC l <* <[0;1;1;0;0] {{QE}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h011B l (0>>r) => Some (hL l (0>>1>>r))
| h011B l (1>>r) => Some (h0110D l r)
| h0110D l (0>>r) => Some (h01100E l r)
| h0110D l (1>>r) => Some (hL l (0>>1>>0>>r))
| h01100E l (0>>r) => Some (h01B (l<:L0111) r)
| h01100E l (1>>r) => Some (h0A (l<:L01100) r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h011B l r)
| h01F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL (l<:L0111) r => Some (hL l ([0;0;1;0]*>r))
| hL (l<:L01100) r => Some (h01B (l<:L01101) r)
| hL (l<:L01101) r => Some (hL l ([0;1;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM12.


Module TM13.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1RD---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1RE---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L0110 | L0111
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h011D(l:list LD)(r:side)
| h0110E(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L0110::ls => toLC ls <* <[0;1;1;0]
| L0111::ls => toLC ls <* <[0;1;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011D l r => toLC l <* <[0;1;1] {{QD}}> r
| h0110E l r => toLC l <* <[0;1;1;0] {{QE}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h011D l (0>>r) => Some (h0110E l r)
| h011D l (1>>r) => Some (hL l (0>>0>>r))
| h0110E l (0>>r) => Some (hL l (0>>1>>0>>r))
| h0110E l (1>>r) => Some (h0A (l<:L0110) r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h011D l r)
| h01F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L0110) r => Some (h01B (l<:L0111) r)
| hL (l<:L0111) r => Some (hL l ([0;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM13.


Module TM14.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_0RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L01000 | L01001
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010B(l:list LD)(r:side)
| h0100D(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h01000E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010B l r => toLC l <* <[0;1;0] {{QB}}> r
| h0100D l r => toLC l <* <[0;1;0;0] {{QD}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h01000E l r => toLC l <* <[0;1;0;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010B l (0>>r) => Some (h0A (l<:L011) r)
| h010B l (1>>r) => Some (h0100D l r)
| h0100D l (0>>r) => Some (h01000E l r)
| h0100D l (1>>r) => Some (h01B (l<:L011) r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h01000E l (0>>r) => Some (hL (l<:L0100) r)
| h01000E l (1>>r) => Some (h0A (l<:L01000) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h010B l r)
| h01F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM14.


Module TM15.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LE_1RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L01000 | L01001 | L0111 | L01100 | L01101
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h011C(l:list LD)(r:side)
| h0111E(l:list LD)(r:side)
| h01100E(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| L01100::ls => toLC ls <* <[0;1;1;0;0]
| L01101::ls => toLC ls <* <[0;1;1;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011C l r => toLC l <* <[0;1;1] {{QC}}> r
| h0111E l r => toLC l <* <[0;1;1;1] {{QE}}> r
| h01100E l r => toLC l <* <[0;1;1;0;0] {{QE}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h011C l (0>>r) => Some (h0111E l r)
| h011C l (1>>r) => Some (hL l (0>>0>>r))
| h0111E l (0>>r) => Some (h01100E l r)
| h0111E l (1>>r) => Some (h0A (l<:L0111) r)
| h01100E l (0>>r) => Some (h01B (l<:L0111) r)
| h01100E l (1>>r) => Some (h0A (l<:L01100) r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h011C l r)
| h01F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL (l<:L0111) r => Some (hL l ([0;0;1;0]*>r))
| hL (l<:L01100) r => Some (h01B (l<:L01101) r)
| hL (l<:L01101) r => Some (hL l ([0;1;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM15.


Module TM16.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0RC---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| h010E(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| h010E l r => toLC l <* <[0;1;0] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h010E l r)
| h01F l (1>>r) => None
| h010E l (0>>r) => Some (hL l (1>>0>>r))
| h010E l (1>>r) => Some (h0A (l<:L010) r)
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM16.


Module TM17.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RB---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L01000 | L01001
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010B(l:list LD)(r:side)
| h0100D(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h01000E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010B l r => toLC l <* <[0;1;0] {{QB}}> r
| h0100D l r => toLC l <* <[0;1;0;0] {{QD}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h01000E l r => toLC l <* <[0;1;0;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010B l (0>>r) => Some (h0A (l<:L011) r)
| h010B l (1>>r) => Some (h0100D l r)
| h0100D l (0>>r) => Some (h01000E l r)
| h0100D l (1>>r) => Some (h01B (l<:L011) r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h01000E l (0>>r) => Some (hL (l<:L0100) r)
| h01000E l (1>>r) => Some (h0A (l<:L01000) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h010B l r)
| h01F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM17.


Module TM18.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_1RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_1RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01 | L010 | L011 | L0100 | L0101 | L01000 | L01001 | L0111 | L01100 | L01101
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h011C(l:list LD)(r:side)
| h0111E(l:list LD)(r:side)
| h01100E(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L01::ls => toLC ls <* <[0;1]
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| L01100::ls => toLC ls <* <[0;1;1;0;0]
| L01101::ls => toLC ls <* <[0;1;1;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011C l r => toLC l <* <[0;1;1] {{QC}}> r
| h0111E l r => toLC l <* <[0;1;1;1] {{QE}}> r
| h01100E l r => toLC l <* <[0;1;1;0;0] {{QE}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h011C l (0>>r) => Some (h0111E l r)
| h011C l (1>>r) => Some (h01B (l<:L01) r)
| h0111E l (0>>r) => Some (h01100E l r)
| h0111E l (1>>r) => Some (h0A (l<:L0111) r)
| h01100E l (0>>r) => Some (h01B (l<:L0111) r)
| h01100E l (1>>r) => Some (h0A (l<:L01100) r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h011C l r)
| h01F l (1>>r) => None
| hL (l<:L01) r => Some (hL l ([1;0]*>r))
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL (l<:L0111) r => Some (h0100E (l<:L01) r)
| hL (l<:L01100) r => Some (h01B (l<:L01101) r)
| hL (l<:L01101) r => Some (hL l ([0;1;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM18.


Module TM19.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0LC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC0LA_0LB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (hL l (0>>r))
| h01F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM19.


Module TM20.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LE---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_1LC---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h00F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h00F l r => toLC l <* <[0;0] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h00F l r)
| h00F l (0>>r) => Some (hL l (1>>r))
| h00F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM20.


Module TM21.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_1LA---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_1LD---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h00F(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h00F l r => toLC l <* <[0;0] {{QF}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h00F l r)
| h00F l (0>>r) => Some (h010D l r)
| h00F l (1>>r) => None
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM21.


Module TM22.
Definition tm := TM_from_str "1RB1RF_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA1RF_0RC1LF_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L010 | L011 | L0100 | L0101 | L01000 | L01001
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h01000E(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01F(l:list LD)(r:side)
| h010C(l:list LD)(r:side)
| h0101E(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0100::ls => toLC ls <* <[0;1;0;0]
| L0101::ls => toLC ls <* <[0;1;0;1]
| L01000::ls => toLC ls <* <[0;1;0;0;0]
| L01001::ls => toLC ls <* <[0;1;0;0;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h01000E l r => toLC l <* <[0;1;0;0;0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01F l r => toLC l <* <[0;1] {{QF}}> r
| h010C l r => toLC l <* <[0;1;0] {{QC}}> r
| h0101E l r => toLC l <* <[0;1;0;1] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (hL (l<:L010) r)
| h0100E l (1>>r) => Some (h0A (l<:L0100) r)
| h01000E l (0>>r) => Some (hL (l<:L0100) r)
| h01000E l (1>>r) => Some (h0A (l<:L01000) r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => Some (h01F l r)
| h01F l (0>>r) => Some (h010C l r)
| h01F l (1>>r) => None
| h010C l (0>>r) => Some (h0101E l r)
| h010C l (1>>r) => Some (hL l (1>>0>>r))
| h0101E l (0>>r) => Some (h01000E l r)
| h0101E l (1>>r) => Some (h0A (l<:L0101) r)
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L0100) r => Some (h01B (l<:L0101) r)
| hL (l<:L0101) r => Some (hL l ([1;0;1;0]*>r))
| hL (l<:L01000) r => Some (h01B (l<:L01001) r)
| hL (l<:L01001) r => Some (h0100E (l<:L011) r)
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM22.


Module TM23.
Definition tm := TM_from_str "1LB0RB_0RC0LE_0LE0RD_1RA1RB_1LF---_1RC0LB".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RF_1LF0RF_0RC0LA".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L01 | L010 | L011
.

Inductive Config :=
| h01A(l:list LD)(r:side)
| h010B(l:list LD)(r:side)
| h0100C(l:list LD)(r:side)
| h01000D(l:list LD)(r:side)
| h01B(l:list LD)(r:side)
| h010C(l:list LD)(r:side)
| h0100D(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L01::ls => toLC ls <* <[0;1]
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01A l r => toLC l <* <[0;1] {{QA}}> r
| h010B l r => toLC l <* <[0;1;0] {{QB}}> r
| h0100C l r => toLC l <* <[0;1;0;0] {{QC}}> r
| h01000D l r => toLC l <* <[0;1;0;0;0] {{QD}}> r
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010C l r => toLC l <* <[0;1;0] {{QC}}> r
| h0100D l r => toLC l <* <[0;1;0;0] {{QD}}> r
| hL l r => toLC l <{{QF}} [1;0] *> r
end.

Definition f x :=
match x with
| h01A l (0>>r) => Some (hL l (1>>r))
| h01A l (1>>r) => Some (h010B l r)
| h010B l (0>>r) => Some (h0100C l r)
| h010B l (1>>r) => Some (hL l (1>>0>>r))
| h0100C l (0>>r) => Some (h01A (l<:L011) r)
| h0100C l (1>>r) => Some (h01000D l r)
| h01000D l (0>>r) => Some (h01A (l<:L01<:L00) r)
| h01000D l (1>>r) => Some (h01B (l<:L01<:L00) r)
| h01B l (0>>r) => Some (h010C l r)
| h01B l (1>>r) => None
| h010C l (0>>r) => Some (hL l (1>>0>>r))
| h010C l (1>>r) => Some (h0100D l r)
| h0100D l (0>>r) => Some (h01A (l<:L010) r)
| h0100D l (1>>r) => Some (h01B (l<:L010) r)
| hL (l<:L00) r => Some (h01A (l<:L01) r)
| hL (l<:L01) r => Some (hL l (1>>0>>r))
| hL (l<:L010) r => Some (h01A (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL [] r => Some (h01A [] (1>>0>>r))
end.

Definition cfg0 := h01A [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E F C D B <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM23.


Module TM24.
Definition tm := TM_from_str "1RB---_1LC0RD_1RF0LD_0RE0LD_0LB1RF_0LF0RA".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LC0RD_1RA---_0RF0LE_0LA1RC".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L01 | L010 | L011
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h01001F(l:list LD)(r:side)
| h010010A(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L01::ls => toLC ls <* <[0;1]
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h01001F l r => toLC l <* <[0;1;0;0;1] {{QF}}> r
| h010010A l r => toLC l <* <[0;1;0;0;1;0] {{QA}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (h01B (l<:L011) r)
| h0100E l (1>>r) => Some (h01001F l r)
| h01001F l (0>>r) => Some (h01B (l<:L01<:L00) r)
| h01001F l (1>>r) => Some (h010010A l r)
| h010010A l (0>>r) => Some (h01B (l<:L010<:L01) r)
| h010010A l (1>>r) => None
| hL (l<:L00) r => Some (h01B (l<:L01) r)
| hL (l<:L01) r => Some (hL l (1>>0>>r))
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E F C <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM24.


Module TM25.
Definition tm := TM_from_str "1LB0RB_0RC0LE_0LE0RD_1RA1RE_1LF---_1RC0LB".
Definition tm' := TM_from_str "1LB---_1RC0LF_0LA0RD_1RE1RA_1LF0RF_0RC0LA".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L01 | L010 | L011
.

Inductive Config :=
| h01A(l:list LD)(r:side)
| h010B(l:list LD)(r:side)
| h0100C(l:list LD)(r:side)
| h01000D(l:list LD)(r:side)
| h01E(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L01::ls => toLC ls <* <[0;1]
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01A l r => toLC l <* <[0;1] {{QA}}> r
| h010B l r => toLC l <* <[0;1;0] {{QB}}> r
| h0100C l r => toLC l <* <[0;1;0;0] {{QC}}> r
| h01000D l r => toLC l <* <[0;1;0;0;0] {{QD}}> r
| h01E l r => toLC l <* <[0;1] {{QE}}> r
| hL l r => toLC l <{{QF}} [1;0] *> r
end.

Definition f x :=
match x with
| h01A l (0>>r) => Some (hL l (1>>r))
| h01A l (1>>r) => Some (h010B l r)
| h010B l (0>>r) => Some (h0100C l r)
| h010B l (1>>r) => Some (hL l (1>>0>>r))
| h0100C l (0>>r) => Some (h01A (l<:L011) r)
| h0100C l (1>>r) => Some (h01000D l r)
| h01000D l (0>>r) => Some (h01A (l<:L01<:L00) r)
| h01000D l (1>>r) => Some (h01E (l<:L01<:L00) r)
| h01E l (0>>r) => Some (hL l (1>>r))
| h01E l (1>>r) => None
| hL (l<:L00) r => Some (h01A (l<:L01) r)
| hL (l<:L01) r => Some (hL l (1>>0>>r))
| hL (l<:L010) r => Some (h01A (l<:L011) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL [] r => Some (h01A [] (1>>0>>r))
end.

Definition cfg0 := h01A [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E F C D A B <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM25.


Module TM26.
Definition tm := TM_from_str "1RB---_1RC0RD_1LD1RF_0LF0LE_1LD0LE_0RB0RA".
Definition tm' := TM_from_str "1LB1RC_0LC0LE_0RD0RF_1RA0RB_1LB0LE_1RD---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01 | L10 | L011 | L0111
.

Inductive Config :=
| h01C(l:list LD)(r:side)
| h011F(l:list LD)(r:side)
| h0110B(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01100D(l:list LD)(r:side)
| h01B(l:list LD)(r:side)
| h011C(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0111F(l:list LD)(r:side)
| h0101C(l:list LD)(r:side)
| h01110B(l:list LD)(r:side)
| h011100D(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L01::ls => toLC ls <* <[0;1]
| L10::ls => toLC ls <* <[1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01C l r => toLC l <* <[0;1] {{QC}}> r
| h011F l r => toLC l <* <[0;1;1] {{QF}}> r
| h0110B l r => toLC l <* <[0;1;1;0] {{QB}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01100D l r => toLC l <* <[0;1;1;0;0] {{QD}}> r
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011C l r => toLC l <* <[0;1;1] {{QC}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0111F l r => toLC l <* <[0;1;1;1] {{QF}}> r
| h0101C l r => toLC l <* <[0;1;0;1] {{QC}}> r
| h01110B l r => toLC l <* <[0;1;1;1;0] {{QB}}> r
| h011100D l r => toLC l <* <[0;1;1;1;0;0] {{QD}}> r
| hL l r => toLC l <{{QD}} [1;0] *> r
end.

Definition f x :=
match x with
| h01C l (0>>r) => Some (hL l (1>>r))
| h01C l (1>>r) => Some (h011F l r)
| h011F l (0>>r) => Some (h0110B l r)
| h011F l (1>>r) => Some (h0A (l<:L011) r)
| h0110B l (0>>r) => Some (h01C (l<:L011) r)
| h0110B l (1>>r) => Some (h01100D l r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => None 
| h01100D l (0>>r) => Some (h01C (l<:L01<:L10) r)
| h01100D l (1>>r) => Some (h01C (l<:L01<:L01) r)
| h01B l (0>>r) => Some (h011C l r) 
| h01B l (1>>r) => Some (h010D l r)
| h011C l (0>>r) => Some (hL l (0>>1>>r)) 
| h011C l (1>>r) => Some (h0111F l r)
| h010D l (0>>r) => Some (h0101C l r) 
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0111F l (0>>r) => Some (h01110B l r) 
| h0111F l (1>>r) => Some (h0A (l<:L0111) r)
| h0101C l (0>>r) => Some (hL l (1>>0>>1>>r)) 
| h0101C l (1>>r) => Some (h011F (l<:L01) r)
| h01110B l (0>>r) => Some (h01C (l<:L0111) r) 
| h01110B l (1>>r) => Some (h011100D l r)
| h011100D l (0>>r) => Some (h01C (l<:L011<:L10) r) 
| h011100D l (1>>r) => Some (h01C (l<:L011<:L01) r)
| hL (l<:L0111) r => Some (hL l ([0;0;1;0]*>r))
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L10) r => Some (h0101C l r)
| hL (l<:L01) r => Some (hL l ([1;0]*>r))
| hL [] r => Some (h01C [] (1>>0>>r))
end.

Definition cfg0 := h01C [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D F <[0;1;1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 F D A B C <[0;1;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM26.


Module TM27.
Definition tm := TM_from_str "1RB---_1RC0RD_1LD1RF_0LF0LE_1LD0LE_0RB0RA".
Definition tm' := TM_from_str "1RB0RC_1LC1RE_0LE0LD_1LC0LD_0RA0RF_1RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01 | L10 | L011 | L0111
.

Inductive Config :=
| h01C(l:list LD)(r:side)
| h011F(l:list LD)(r:side)
| h0110B(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01100D(l:list LD)(r:side)
| h01B(l:list LD)(r:side)
| h011C(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0111F(l:list LD)(r:side)
| h0101C(l:list LD)(r:side)
| h01110B(l:list LD)(r:side)
| h011100D(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L01::ls => toLC ls <* <[0;1]
| L10::ls => toLC ls <* <[1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01C l r => toLC l <* <[0;1] {{QC}}> r
| h011F l r => toLC l <* <[0;1;1] {{QF}}> r
| h0110B l r => toLC l <* <[0;1;1;0] {{QB}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01100D l r => toLC l <* <[0;1;1;0;0] {{QD}}> r
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011C l r => toLC l <* <[0;1;1] {{QC}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0111F l r => toLC l <* <[0;1;1;1] {{QF}}> r
| h0101C l r => toLC l <* <[0;1;0;1] {{QC}}> r
| h01110B l r => toLC l <* <[0;1;1;1;0] {{QB}}> r
| h011100D l r => toLC l <* <[0;1;1;1;0;0] {{QD}}> r
| hL l r => toLC l <{{QD}} [1;0] *> r
end.

Definition f x :=
match x with
| h01C l (0>>r) => Some (hL l (1>>r))
| h01C l (1>>r) => Some (h011F l r)
| h011F l (0>>r) => Some (h0110B l r)
| h011F l (1>>r) => Some (h0A (l<:L011) r)
| h0110B l (0>>r) => Some (h01C (l<:L011) r)
| h0110B l (1>>r) => Some (h01100D l r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => None 
| h01100D l (0>>r) => Some (h01C (l<:L01<:L10) r)
| h01100D l (1>>r) => Some (h01C (l<:L01<:L01) r)
| h01B l (0>>r) => Some (h011C l r) 
| h01B l (1>>r) => Some (h010D l r)
| h011C l (0>>r) => Some (hL l (0>>1>>r)) 
| h011C l (1>>r) => Some (h0111F l r)
| h010D l (0>>r) => Some (h0101C l r) 
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0111F l (0>>r) => Some (h01110B l r) 
| h0111F l (1>>r) => Some (h0A (l<:L0111) r)
| h0101C l (0>>r) => Some (hL l (1>>0>>1>>r)) 
| h0101C l (1>>r) => Some (h011F (l<:L01) r)
| h01110B l (0>>r) => Some (h01C (l<:L0111) r) 
| h01110B l (1>>r) => Some (h011100D l r)
| h011100D l (0>>r) => Some (h01C (l<:L011<:L10) r) 
| h011100D l (1>>r) => Some (h01C (l<:L011<:L01) r)
| hL (l<:L0111) r => Some (hL l ([0;0;1;0]*>r))
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L10) r => Some (h0101C l r)
| hL (l<:L01) r => Some (hL l ([1;0]*>r))
| hL [] r => Some (h01C [] (1>>0>>r))
end.

Definition cfg0 := h01C [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D F <[0;1;1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 F A B C E (@nil Sym).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM27.


Module TM28.
Definition tm := TM_from_str "1LB1RD_1LC0LB_0LD0LB_0RE0RF_1RA0RC_1RE---".
Definition tm' := TM_from_str "1LB0LA_0LC0LA_0RD0RF_1RE0RB_1LA1RC_1RD---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01 | L10 | L011 | L0111
.

Inductive Config :=
| h01C(l:list LD)(r:side)
| h011F(l:list LD)(r:side)
| h0110B(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01100D(l:list LD)(r:side)
| h01B(l:list LD)(r:side)
| h011C(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0111F(l:list LD)(r:side)
| h0101C(l:list LD)(r:side)
| h01110B(l:list LD)(r:side)
| h011100D(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L01::ls => toLC ls <* <[0;1]
| L10::ls => toLC ls <* <[1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01C l r => toLC l <* <[0;1] {{QC}}> r
| h011F l r => toLC l <* <[0;1;1] {{QF}}> r
| h0110B l r => toLC l <* <[0;1;1;0] {{QB}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01100D l r => toLC l <* <[0;1;1;0;0] {{QD}}> r
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011C l r => toLC l <* <[0;1;1] {{QC}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0111F l r => toLC l <* <[0;1;1;1] {{QF}}> r
| h0101C l r => toLC l <* <[0;1;0;1] {{QC}}> r
| h01110B l r => toLC l <* <[0;1;1;1;0] {{QB}}> r
| h011100D l r => toLC l <* <[0;1;1;1;0;0] {{QD}}> r
| hL l r => toLC l <{{QD}} [1;0] *> r
end.

Definition f x :=
match x with
| h01C l (0>>r) => Some (hL l (1>>r))
| h01C l (1>>r) => Some (h011F l r)
| h011F l (0>>r) => Some (h0110B l r)
| h011F l (1>>r) => Some (h0A (l<:L011) r)
| h0110B l (0>>r) => Some (h01C (l<:L011) r)
| h0110B l (1>>r) => Some (h01100D l r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => None 
| h01100D l (0>>r) => Some (h01C (l<:L01<:L10) r)
| h01100D l (1>>r) => Some (h01C (l<:L01<:L01) r)
| h01B l (0>>r) => Some (h011C l r) 
| h01B l (1>>r) => Some (h010D l r)
| h011C l (0>>r) => Some (hL l (0>>1>>r)) 
| h011C l (1>>r) => Some (h0111F l r)
| h010D l (0>>r) => Some (h0101C l r) 
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0111F l (0>>r) => Some (h01110B l r) 
| h0111F l (1>>r) => Some (h0A (l<:L0111) r)
| h0101C l (0>>r) => Some (hL l (1>>0>>1>>r)) 
| h0101C l (1>>r) => Some (h011F (l<:L01) r)
| h01110B l (0>>r) => Some (h01C (l<:L0111) r) 
| h01110B l (1>>r) => Some (h011100D l r)
| h011100D l (0>>r) => Some (h01C (l<:L011<:L10) r) 
| h011100D l (1>>r) => Some (h01C (l<:L011<:L01) r)
| hL (l<:L0111) r => Some (hL l ([0;0;1;0]*>r))
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L10) r => Some (h0101C l r)
| hL (l<:L01) r => Some (hL l ([1;0]*>r))
| hL [] r => Some (h01C [] (1>>0>>r))
end.

Definition cfg0 := h01C [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 F E A C D <[0;1;1;0;1;1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 F D E B C <[0;1;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM28.


Module TM29.
Definition tm := TM_from_str "1LB1RC_0LC0LE_0RD0RF_1RA0RB_1LB0LA_1RD---".
Definition tm' := TM_from_str "1RB---_1RC0RD_1LD1RF_0LF0LE_1LD0LC_0RB0RA".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01 | L10 | L011 | L0111
.

Inductive Config :=
| h01C(l:list LD)(r:side)
| h011F(l:list LD)(r:side)
| h0110B(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01100D(l:list LD)(r:side)
| h01B(l:list LD)(r:side)
| h011C(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0111F(l:list LD)(r:side)
| h0101C(l:list LD)(r:side)
| h01110B(l:list LD)(r:side)
| h011100D(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L01::ls => toLC ls <* <[0;1]
| L10::ls => toLC ls <* <[1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01C l r => toLC l <* <[0;1] {{QC}}> r
| h011F l r => toLC l <* <[0;1;1] {{QF}}> r
| h0110B l r => toLC l <* <[0;1;1;0] {{QB}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01100D l r => toLC l <* <[0;1;1;0;0] {{QD}}> r
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011C l r => toLC l <* <[0;1;1] {{QC}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0111F l r => toLC l <* <[0;1;1;1] {{QF}}> r
| h0101C l r => toLC l <* <[0;1;0;1] {{QC}}> r
| h01110B l r => toLC l <* <[0;1;1;1;0] {{QB}}> r
| h011100D l r => toLC l <* <[0;1;1;1;0;0] {{QD}}> r
| hL l r => toLC l <{{QD}} [1;0] *> r
end.

Definition f x :=
match x with
| h01C l (0>>r) => Some (hL l (1>>r))
| h01C l (1>>r) => Some (h011F l r)
| h011F l (0>>r) => Some (h0110B l r)
| h011F l (1>>r) => Some (h0A (l<:L011) r)
| h0110B l (0>>r) => Some (h01C (l<:L011) r)
| h0110B l (1>>r) => Some (h01100D l r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => None 
| h01100D l (0>>r) => Some (h01C (l<:L01<:L10) r)
| h01100D l (1>>r) => Some (h01C (l<:L01<:L01) r)
| h01B l (0>>r) => Some (h011C l r) 
| h01B l (1>>r) => Some (h010D l r)
| h011C l (0>>r) => Some (hL l (0>>1>>r)) 
| h011C l (1>>r) => Some (h0111F l r)
| h010D l (0>>r) => Some (h0101C l r) 
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0111F l (0>>r) => Some (h01110B l r) 
| h0111F l (1>>r) => Some (h0A (l<:L0111) r)
| h0101C l (0>>r) => Some (hL l (1>>0>>1>>r)) 
| h0101C l (1>>r) => Some (h011F (l<:L01) r)
| h01110B l (0>>r) => Some (h01C (l<:L0111) r) 
| h01110B l (1>>r) => Some (h011100D l r)
| h011100D l (0>>r) => Some (h01C (l<:L011<:L10) r) 
| h011100D l (1>>r) => Some (h01C (l<:L011<:L01) r)
| hL (l<:L0111) r => Some (h0110B (l<:L01) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L10) r => Some (h0101C l r)
| hL (l<:L01) r => Some (hL l ([1;0]*>r))
| hL [] r => Some (h01C [] (1>>0>>r))
end.

Definition cfg0 := h01C [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 F D A B C <[0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D F <[0;1;1;0;1;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM29.


Module TM30.
Definition tm := TM_from_str "1LB1RC_0LC0LE_0RD0RF_1RA0RB_1LB0LA_1RD---".
Definition tm' := TM_from_str "1RB0RC_1LC1RE_0LE0LD_1LC0LB_0RA0RF_1RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01 | L10 | L011 | L0111
.

Inductive Config :=
| h01C(l:list LD)(r:side)
| h011F(l:list LD)(r:side)
| h0110B(l:list LD)(r:side)
| h0A(l:list LD)(r:side)
| h01100D(l:list LD)(r:side)
| h01B(l:list LD)(r:side)
| h011C(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0111F(l:list LD)(r:side)
| h0101C(l:list LD)(r:side)
| h01110B(l:list LD)(r:side)
| h011100D(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L01::ls => toLC ls <* <[0;1]
| L10::ls => toLC ls <* <[1;0]
| L011::ls => toLC ls <* <[0;1;1]
| L0111::ls => toLC ls <* <[0;1;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01C l r => toLC l <* <[0;1] {{QC}}> r
| h011F l r => toLC l <* <[0;1;1] {{QF}}> r
| h0110B l r => toLC l <* <[0;1;1;0] {{QB}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h01100D l r => toLC l <* <[0;1;1;0;0] {{QD}}> r
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h011C l r => toLC l <* <[0;1;1] {{QC}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0111F l r => toLC l <* <[0;1;1;1] {{QF}}> r
| h0101C l r => toLC l <* <[0;1;0;1] {{QC}}> r
| h01110B l r => toLC l <* <[0;1;1;1;0] {{QB}}> r
| h011100D l r => toLC l <* <[0;1;1;1;0;0] {{QD}}> r
| hL l r => toLC l <{{QD}} [1;0] *> r
end.

Definition f x :=
match x with
| h01C l (0>>r) => Some (hL l (1>>r))
| h01C l (1>>r) => Some (h011F l r)
| h011F l (0>>r) => Some (h0110B l r)
| h011F l (1>>r) => Some (h0A (l<:L011) r)
| h0110B l (0>>r) => Some (h01C (l<:L011) r)
| h0110B l (1>>r) => Some (h01100D l r)
| h0A l (0>>r) => Some (h01B l r)
| h0A l (1>>r) => None 
| h01100D l (0>>r) => Some (h01C (l<:L01<:L10) r)
| h01100D l (1>>r) => Some (h01C (l<:L01<:L01) r)
| h01B l (0>>r) => Some (h011C l r) 
| h01B l (1>>r) => Some (h010D l r)
| h011C l (0>>r) => Some (hL l (0>>1>>r)) 
| h011C l (1>>r) => Some (h0111F l r)
| h010D l (0>>r) => Some (h0101C l r) 
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0111F l (0>>r) => Some (h01110B l r) 
| h0111F l (1>>r) => Some (h0A (l<:L0111) r)
| h0101C l (0>>r) => Some (hL l (1>>0>>1>>r)) 
| h0101C l (1>>r) => Some (h011F (l<:L01) r)
| h01110B l (0>>r) => Some (h01C (l<:L0111) r) 
| h01110B l (1>>r) => Some (h011100D l r)
| h011100D l (0>>r) => Some (h01C (l<:L011<:L10) r) 
| h011100D l (1>>r) => Some (h01C (l<:L011<:L01) r)
| hL (l<:L0111) r => Some (h0110B (l<:L01) r)
| hL (l<:L011) r => Some (hL l ([0;1;0]*>r))
| hL (l<:L10) r => Some (h0101C l r)
| hL (l<:L01) r => Some (hL l ([1;0]*>r))
| hL [] r => Some (h01C [] (1>>0>>r))
end.

Definition cfg0 := h01C [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 F D A B C <[0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 F A B C E (@nil Sym).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM30.


Module TM31.
Definition tm := TM_from_str "1RB---_1LC0RC_0RF0LD_1LE0LB_1RF0LD_0LD0RA".
Definition tm' := TM_from_str "1LB0LE_1RC0LA_0LA0RD_1RE---_1LF0RF_0RC0LA".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L01 | L010 | L011
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h01001F(l:list LD)(r:side)
| hL(l:list LD)(r:side)
| hL'(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L01::ls => toLC ls <* <[0;1]
| L010::ls => toLC ls <* <[0;1;0]
| L011::ls => toLC ls <* <[0;1;1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QC}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QF}}> r
| h01001F l r => toLC l <* <[0;1;0;0;0] {{QA}}> r
| hL l r => toLC l <{{QE}} [1;0] *> r
| hL' l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (h01B (l<:L011) r)
| h0100E l (1>>r) => Some (h01001F l r)
| h01001F l (0>>r) => Some (h01B (l<:L01<:L00) r)
| h01001F l (1>>r) => None 
| hL (l<:L00) r => Some (h01B (l<:L01) r)
| hL (l<:L01) r => Some (hL l (1>>0>>r))
| hL (l<:L010) r => Some (h01B (l<:L011) r)
| hL (l<:L011) r => Some (hL' l ([0;1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
| hL' (l<:L00) r => Some (h01B (l<:L00) r)
| hL' (l<:L01) r => Some (hL l (1>>0>>r))
| hL' (l<:L010) r => Some (h01B (l<:L010) r)
| hL' (l<:L011) r => Some (hL' l ([0;1;0]*>r))
| hL' [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L011 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D E F B C <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM31.


Module TM32.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE1LF_0LB0RA_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC1LF_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01(a b:nat)
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(l0:LD)(r:side)
| hF(l:list LD)(l0:LD)(r:side)
| h0C(l:list LD)(l0:LD)(r:side)
| h01E(l:list LD)(l0:LD)(r:side)
| h000E(l:list LD)(l0:LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L01 a b)::ls => toLC ls <* <[0;1] <* <[1]^^a <* <[0]^^b
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l l0 r => toLC (l0::l) <* <[0] {{QA}}> r
| hF l l0 r => toLC (l0::l) <* <[] {{QF}}> r
| h0C l l0 r => toLC (l0::l) <* <[0] {{QC}}> r
| h01E l l0 r => toLC (l0::l) <* <[0;1] {{QE}}> r
| h000E l l0 r => toLC (l0::l) <* <[0;0;0] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (h01B (l<:(L01 1 0)) r)
| h0100E l (1>>r) => Some (h0A l (L01 0 2) r)
| h0A l l0 (0>>r) => Some (h01B (l<:l0) r)
| h0A l (L01 a b) (1>>r) => Some (hF l (L01 a (S(S b))) r)
| hF l l0 (0>>r) => Some (h0C l l0 r)
| hF l l0 (1>>r) => None
| h0C l l0 (0>>r) => Some (h01E l l0 r)
| h0C l l0 (1>>r) => Some (hL (l<:l0) r)
| h01E l l0 (0>>r) => Some (h000E l l0 r)
| h01E l l0 (1>>r) => Some (h0A (l<:l0) (L01 0 0) r)
| h000E l l0 (0>>r) => Some (h01B (l<:l0<:(L01 0 0)) r)
| h000E l (L01 a b) (1>>r) => Some (h0A l (L01 a (S(S(S b)))) r)
| hL (l<:(L01 a (S (S b)))) r => Some (h01B (l<:(L01 a b)<:(L01 0 0)) r)
| hL (l<:(L01 a 1)) r => Some (h01B (l<:(L01 (S a) 0)) r)
| hL (l<:(L01 0 0)) r => Some (hL l (1>>0>>r))
| hL (l<:(L01 1 0)) r => Some (hL l (0>>1>>0>>r))
| hL (l<:(L01 _ 0)) r => None
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L01 _ _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM32.


Module TM33.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01(a b:nat)
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(l0:LD)(r:side)
| hF(l:list LD)(l0:LD)(r:side)
| h0C(l:list LD)(l0:LD)(r:side)
| h01E(l:list LD)(l0:LD)(r:side)
| h000E(l:list LD)(l0:LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L01 a b)::ls => toLC ls <* <[0;1] <* <[1]^^a <* <[0]^^b
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l l0 r => toLC (l0::l) <* <[0] {{QA}}> r
| hF l l0 r => toLC (l0::l) <* <[] {{QF}}> r
| h0C l l0 r => toLC (l0::l) <* <[0] {{QC}}> r
| h01E l l0 r => toLC (l0::l) <* <[0;1] {{QE}}> r
| h000E l l0 r => toLC (l0::l) <* <[0;0;0] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (h01B (l<:(L01 1 0)) r)
| h0100E l (1>>r) => Some (h0A l (L01 0 2) r)
| h0A l l0 (0>>r) => Some (h01B (l<:l0) r)
| h0A l (L01 a b) (1>>r) => Some (hF l (L01 a (S(S b))) r)
| hF l l0 (0>>r) => Some (h0C l l0 r)
| hF l l0 (1>>r) => None
| h0C l l0 (0>>r) => Some (h01E l l0 r)
| h0C l l0 (1>>r) => Some (hL (l<:l0) r)
| h01E l l0 (0>>r) => Some (h000E l l0 r)
| h01E l l0 (1>>r) => Some (h0A (l<:l0) (L01 0 0) r)
| h000E l l0 (0>>r) => Some (h01B (l<:l0<:(L01 0 0)) r)
| h000E l (L01 a b) (1>>r) => Some (h0A l (L01 a (S(S(S b)))) r)
| hL (l<:(L01 a (S (S b)))) r => Some (h01B (l<:(L01 a b)<:(L01 0 0)) r)
| hL (l<:(L01 a 1)) r => Some (h01B (l<:(L01 (S a) 0)) r)
| hL (l<:(L01 a 0)) r => Some (hL l ([0]^^a*>[1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L01 _ _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM33.


Module TM34.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LB_0LB0RA_0RC---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LA_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01(a b:nat)
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(l0:LD)(r:side)
| hF(l:list LD)(l0:LD)(r:side)
| h0C(l:list LD)(l0:LD)(r:side)
| h01E(l:list LD)(l0:LD)(r:side)
| h000E(l:list LD)(l0:LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L01 a b)::ls => toLC ls <* <[0;1] <* <[1]^^a <* <[0]^^b
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l l0 r => toLC (l0::l) <* <[0] {{QA}}> r
| hF l l0 r => toLC (l0::l) <* <[] {{QF}}> r
| h0C l l0 r => toLC (l0::l) <* <[0] {{QC}}> r
| h01E l l0 r => toLC (l0::l) <* <[0;1] {{QE}}> r
| h000E l l0 r => toLC (l0::l) <* <[0;0;0] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (h01B (l<:(L01 1 0)) r)
| h0100E l (1>>r) => Some (h0A l (L01 0 2) r)
| h0A l l0 (0>>r) => Some (h01B (l<:l0) r)
| h0A l (L01 a b) (1>>r) => Some (hF l (L01 a (S(S b))) r)
| hF l l0 (0>>r) => Some (h0C l l0 r)
| hF l l0 (1>>r) => None
| h0C l l0 (0>>r) => Some (h01E l l0 r)
| h0C l l0 (1>>r) => Some (hL (l<:l0) r)
| h01E l l0 (0>>r) => Some (h000E l l0 r)
| h01E l l0 (1>>r) => Some (h0A (l<:l0) (L01 0 0) r)
| h000E l l0 (0>>r) => Some (h01B (l<:l0<:(L01 0 0)) r)
| h000E l (L01 a b) (1>>r) => Some (h0A l (L01 a (S(S(S b)))) r)
| hL (l<:(L01 a (S (S b)))) r => Some (h01B (l<:(L01 a b)<:(L01 0 0)) r)
| hL (l<:(L01 a 1)) r => Some (h01B (l<:(L01 (S a) 0)) r)
| hL (l<:(L01 0 0)) r => Some (hL l ([1;0]*>r))
| hL (l<:(L01 1 0)) r => Some (hL l ([0;1;0]*>r))
| hL (l<:(L01 (S(S a)) 0)) r => Some (h0100E (l<:(L01 a 0)) r)
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L01 _ _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM34.


Module TM35.
Definition tm := TM_from_str "1RB0RF_1LC0RD_1RE0LD_0RE0LD_0LB0RA_0RD---".
Definition tm' := TM_from_str "1LB0RE_1RC0LE_0LA0RD_1RA0RF_0RC0LE_0RE---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01(a b:nat)
.

Inductive Config :=
| h01B(l:list LD)(r:side)
| h010D(l:list LD)(r:side)
| h0100E(l:list LD)(r:side)
| h0A(l:list LD)(l0:LD)(r:side)
| h00F(l:list LD)(l0:LD)(r:side)
| h000D(l:list LD)(l0:LD)(r:side)
| h0000E(l:list LD)(l0:LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L01 a b)::ls => toLC ls <* <[0;1] <* <[1]^^a <* <[0]^^b
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h01B l r => toLC l <* <[0;1] {{QB}}> r
| h010D l r => toLC l <* <[0;1;0] {{QD}}> r
| h0100E l r => toLC l <* <[0;1;0;0] {{QE}}> r
| h0A l l0 r => toLC (l0::l) <* <[0] {{QA}}> r
| h00F l l0 r => toLC (l0::l) <* <[0;0] {{QF}}> r
| h000D l l0 r => toLC (l0::l) <* <[0;0;0] {{QD}}> r
| h0000E l l0 r => toLC (l0::l) <* <[0;0;0;0] {{QE}}> r
| hL l r => toLC l <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| h01B l (0>>r) => Some (hL l (1>>r))
| h01B l (1>>r) => Some (h010D l r)
| h010D l (0>>r) => Some (h0100E l r)
| h010D l (1>>r) => Some (hL l (1>>0>>r))
| h0100E l (0>>r) => Some (h01B (l<:(L01 1 0)) r)
| h0100E l (1>>r) => Some (h0A l (L01 0 2) r)
| h0A l l0 (0>>r) => Some (h01B (l<:l0) r)
| h0A l l0 (1>>r) => Some (h00F l l0 r)
| h00F l l0 (0>>r) => Some (h000D l l0 r)
| h00F l l0 (1>>r) => None
| h000D l l0 (0>>r) => Some (h0000E l l0 r)
| h000D l l0 (1>>r) => Some (h01B (l<:l0<:(L01 0 0)) r)
| h0000E l (L01 a b) (0>>r) => Some (h01B (l<:(L01 a (S b))<:(L01 0 0)) r)
| h0000E l (L01 a b) (1>>r) => Some (h0A l (L01 a (S(S(S(S b))))) r)
| hL (l<:(L01 a (S (S b)))) r => Some (h01B (l<:(L01 a b)<:(L01 0 0)) r)
| hL (l<:(L01 a 1)) r => Some (h01B (l<:(L01 (S a) 0)) r)
| hL (l<:(L01 a 0)) r => Some (hL l ([0]^^a*>[1;0]*>r))
| hL [] r => Some (h01B [] (1>>0>>r))
end.

Definition cfg0 := h01B [] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L01 _ _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D A B E C F <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM35.


Module TM36.
Definition tm := TM_from_str "1RB0LC_1LA1RE_0RD1LB_0LB---_1RF0RE_1RC0RA".
Definition tm' := TM_from_str "1LB1RC_1RA0LE_1RD0RC_1RE0RB_0RF1LA_0LA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L01(a b:nat)
.

Inductive Config :=
| hB(l:list LD)(m:nat)(r:side)
| hE(l:list LD)(m:nat)(r:side)
| hF(l:list LD)(m:nat)(r:side)
| hC(l:list LD)(m:nat)(r:side)
| h0E(l:list LD)(m:LD)(r:side)
| h0A(l:list LD)(r:side)
| h0D(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L01 a b)::ls => toLC ls <* <[0;1] <* <[1]^^a <* <[0]^^b
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hB l m r => toLC l <* <[0;1] <* [1]^^m {{QB}}> r
| hE l m r => toLC l <* <[0;1] <* [1]^^m {{QE}}> r
| hF l m r => toLC l <* <[0;1] <* [1]^^m {{QF}}> r
| hC l m r => toLC l <* <[0;1] <* [1]^^m {{QC}}> r
| h0E l l0 r => toLC (l<:l0) <* <[0] {{QE}}> r
| h0A l r => toLC l <* <[0] {{QA}}> r
| h0D l r => toLC l <* <[0] {{QD}}> r
| hL l r => toLC l <{{QA}} [1] *> r
end.

Definition f x :=
match x with
| hB l m (0>>r) => Some (hL (l<:(L01 m 0)) r)
| hB l m (1>>r) => Some (hE l (S m) r)
| hE l m (0>>r) => Some (hF l (S m) r)
| hE l m (1>>r) => Some (h0E l (L01 m 0) r)
| hF l m (0>>r) => Some (hC l (S m) r)
| hF l m (1>>r) => Some (h0A (l<:(L01 m 0)) r)
| hC l m (0>>r) => Some (h0D (l<:(L01 m 0)) r)
| hC l m (1>>r) => Some (h0E l (L01 m 0) r)
| h0E l m (0>>r) => Some (hF (l<:m) 0 r)
| h0E l (L01 a b) (1>>r) => Some (h0E l (L01 a (S b)) r)
| h0A l (0>>r) => Some (hB l 0 r)
| h0A l (1>>r) => Some (hL l (0>>r))
| h0D l (0>>r) => Some (hL l (0>>r))
| h0D l (1>>r) => None
| hL (l<:(L01 0 0)) r => Some (hL l (0>>1>>r))
| hL (l<:(L01 1 0)) r => Some (hL l (1>>0>>1>>r))
| hL (l<:(L01 (S(S a)) 0)) r => Some (h0A (l<:(L01 a 0)<:(L01 0 0)) r)
| hL (l<:(L01 a 1)) r => Some (hE l (S(S a)) r)
| hL (l<:(L01 a (S(S b)))) r => Some (hE (l<:(L01 a b)) 1 r)
| hL [] r => Some (hE [] 1 r)
end.

Definition cfg0 := hL [] ([0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L01 _ _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (@nil Sym).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B A E F C D <[1;1;0;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM36.


Module TM37.
Definition tm := TM_from_str "1LB0RD_0LC0LB_0RD1LB_1RD1RE_1RF---_0RA1LA".
Definition tm' := TM_from_str "1RB---_0RC1LC_1LD0RF_0LE0LD_0RF1LD_1RF1RA".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1 | L10 | L100
.

Inductive Config :=
| hD(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| h11F(l:list LD)(r:side)
| h10A(l:list LD)(r:side)
| hL(l:list LD)(r:side).

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L1::ls => toLC ls <* <[1]
| L10::ls => toLC ls <* <[1;0]
| L100::ls => toLC ls <* <[1;0;0]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hD l r => toLC l <* <[] {{QD}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| h11F l r => toLC l <* <[1;1] {{QF}}> r
| h10A l r => toLC l <* <[1;0] {{QA}}> r
| hL l r => toLC l <{{QB}} r
end.

Definition f x :=
match x with
| hD l (0>>r) => Some (hD (l<:L1) r)
| hD l (1>>r) => Some (h1E l r)
| h1E l (0>>r) => Some (h11F l r)
| h1E l (1>>r) => None
| h11F l (0>>r) => Some (h10A (l<:L1) r)
| h11F l (1>>r) => Some (h1E (l<:L10) r)
| h10A l (0>>r) => Some (hL l (1>>0>>1>>r))
| h10A l (1>>r) => Some (hD (l<:L100) r)
| hL (l<:L1) r => Some (hL l (0>>r))
| hL (l<:L10) r => Some (hL l (1>>0>>r))
| hL (l<:L100) r => Some (hD (l<:L10<:L1) r)
| hL [] r => Some (hD [] (0>>r))
end.

Definition cfg0 := hD [] ([0;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B D E F <[1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C D F A B (@nil Sym).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM37.


Module TM38.
Definition tm := TM_from_str "1RB0LF_1RC0LD_1RD0RB_1LE0RC_---0LA_1LA0LF".
Definition tm' := TM_from_str "1RB0LC_1RC0RA_1LD0RB_---0LE_1RA0LF_1LE0LF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1 | L0
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h1C(l:list LD)(r:side)
| h1D(l:list LD)(r:side)
| h0C(l:list LD)(r:side)
| h10B(l:list LD)(r:side)
| h00B(l:list LD)(r:side)
| hL(l:list LD)(r:side)
| hL'(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L1::ls => toLC ls <* <[1]
| L0::ls => toLC ls <* <[0]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1B l r => toLC l <* <[1] {{QB}}> r
| h1C l r => toLC l <* <[1] {{QC}}> r
| h1D l r => toLC l <* <[1] {{QD}}> r
| h0C l r => toLC l <* <[0] {{QC}}> r
| h10B l r => toLC l <* <[1;0] {{QB}}> r
| h00B l r => toLC l <* <[0;0] {{QB}}> r
| hL l r => toLC l <{{QA}} r
| hL' l r => toLC l <{{QF}} r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h1C (l<:L1) r)
| h1B l (1>>r) => Some (h1D (l<:L0) r)
| h1C l (0>>r) => Some (h1D (l<:L1) r)
| h1C l (1>>r) => Some (h10B l r)
| h1D l (0>>r) => Some (hL l (0>>1>>r))
| h1D l (1>>r) => Some (h0C (l<:L1) r)
| h0C l (0>>r) => Some (h1D (l<:L0) r)
| h0C l (1>>r) => Some (h00B l r)
| h10B l (0>>r) => Some (h1C (l<:L1<:L0) r)
| h10B l (1>>r) => Some (hL l (0>>1>>0>>r))
| h00B l (0>>r) => Some (h1C (l<:L0<:L0) r)
| h00B l (1>>r) => None
| hL (l<:L0) r => Some (h1B l r)
| hL (l<:L1) r => Some (hL' l (0>>r))
| hL' (l<:L0) r => Some (hL l (1>>r))
| hL' (l<:L1) r => Some (hL' l (0>>r))
| hL [] r => Some (h1C [L0] r)
| hL' [] r => Some (h1C [L0] r)
end.

Definition cfg0 := hL [] ([1;0;1;0;1;0;0;1;0;0;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D F <[1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E A B C F <[1;1;0;1;0;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM38.


Module TM39.
Definition tm := TM_from_str "1RB0LF_1RC0LD_1RD0RB_1LE0RC_---0LA_1LA0LF".
Definition tm' := TM_from_str "1RB0RE_1LC0RA_---0LD_1RE0LF_1RA0LB_1LD0LF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1 | L0
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h1C(l:list LD)(r:side)
| h1D(l:list LD)(r:side)
| h0C(l:list LD)(r:side)
| h10B(l:list LD)(r:side)
| h00B(l:list LD)(r:side)
| hL(l:list LD)(r:side)
| hL'(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L1::ls => toLC ls <* <[1]
| L0::ls => toLC ls <* <[0]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1B l r => toLC l <* <[1] {{QB}}> r
| h1C l r => toLC l <* <[1] {{QC}}> r
| h1D l r => toLC l <* <[1] {{QD}}> r
| h0C l r => toLC l <* <[0] {{QC}}> r
| h10B l r => toLC l <* <[1;0] {{QB}}> r
| h00B l r => toLC l <* <[0;0] {{QB}}> r
| hL l r => toLC l <{{QA}} r
| hL' l r => toLC l <{{QF}} r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h1C (l<:L1) r)
| h1B l (1>>r) => Some (h1D (l<:L0) r)
| h1C l (0>>r) => Some (h1D (l<:L1) r)
| h1C l (1>>r) => Some (h10B l r)
| h1D l (0>>r) => Some (hL l (0>>1>>r))
| h1D l (1>>r) => Some (h0C (l<:L1) r)
| h0C l (0>>r) => Some (h1D (l<:L0) r)
| h0C l (1>>r) => Some (h00B l r)
| h10B l (0>>r) => Some (h1C (l<:L1<:L0) r)
| h10B l (1>>r) => Some (hL l (0>>1>>0>>r))
| h00B l (0>>r) => Some (h1C (l<:L0<:L0) r)
| h00B l (1>>r) => None
| hL (l<:L0) r => Some (h1B l r)
| hL (l<:L1) r => Some (hL' l (0>>r))
| hL' (l<:L0) r => Some (hL l (1>>r))
| hL' (l<:L1) r => Some (hL' l (0>>r))
| hL [] r => Some (h1C [L0] r)
| hL' [] r => Some (h1C [L0] r)
end.

Definition cfg0 := hL [] ([1;0;1;0;1;0;0;1;0;0;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D F <[1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D E A B F <[1;1;0;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM39.


Module TM40.
Definition tm := TM_from_str "1RB1RD_0LC---_1LD1LC_1RE0RE_0RF0LA_1RA0RE".
Definition tm' := TM_from_str "1LB1LA_1RC0RC_0RE0LD_1RF1RB_1RD0RC_0LA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L10 | L1
.

Inductive Config :=
| h1E(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| h0E(l:list LD)(r:side)
| hA(l:list LD)(r:side)
| h1B(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1E l r => toLC l <* <[1] {{QE}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| h0E l r => toLC l <* <[0] {{QE}}> r
| hA l r => toLC l <* <[] {{QA}}> r
| h1B l r => toLC l <* <[1] {{QB}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| hL l r => toLC l <{{QC}} [1] *> r
end.

Definition f x :=
match x with
| h1E l (0>>r) => Some (hF (l<:L10) r)
| h1E l (1>>r) => Some (h1E (l<:L1) r)
| hF l (0>>r) => Some (hA (l<:L1) r)
| hF l (1>>r) => Some (h0E l r)
| h0E l (0>>r) => Some (hF (l<:L00) r)
| h0E l (1>>r) => Some (hL l (0>>r)) 
| hA l (0>>r) => Some (h1B l r)
| hA l (1>>r) => Some (hD (l<:L1) r)
| h1B l (0>>r) => Some (hL l (0>>r))
| h1B l (1>>r) => None
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => Some (h0E l r)
| hL (l<:L00) r => Some (h1E (l<:L1<:L1) r)
| hL (l<:L10) r => Some (hL l (0>>1>>r))
| hL (l<:L1) r => Some (hL l (1>>r))
| hL [] r => Some (h1E [] (1>>1>>r))
end.

Definition cfg0 := hL [] ([1;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D F A B C E <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM40.


Module TM41.
Definition tm := TM_from_str "1RB1RD_0LC---_1LD1LC_1RE0RE_0RF0LA_1RA0RE".
Definition tm' := TM_from_str "1RB0RB_0RC0LD_1RD0RB_1RE1RA_0LF---_1LA1LF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L10 | L1
.

Inductive Config :=
| h1E(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| h0E(l:list LD)(r:side)
| hA(l:list LD)(r:side)
| h1B(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1E l r => toLC l <* <[1] {{QE}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| h0E l r => toLC l <* <[0] {{QE}}> r
| hA l r => toLC l <* <[] {{QA}}> r
| h1B l r => toLC l <* <[1] {{QB}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| hL l r => toLC l <{{QC}} [1] *> r
end.

Definition f x :=
match x with
| h1E l (0>>r) => Some (hF (l<:L10) r)
| h1E l (1>>r) => Some (h1E (l<:L1) r)
| hF l (0>>r) => Some (hA (l<:L1) r)
| hF l (1>>r) => Some (h0E l r)
| h0E l (0>>r) => Some (hF (l<:L00) r)
| h0E l (1>>r) => Some (hL l (0>>r)) 
| hA l (0>>r) => Some (h1B l r)
| hA l (1>>r) => Some (hD (l<:L1) r)
| h1B l (0>>r) => Some (hL l (0>>r))
| h1B l (1>>r) => None
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => Some (h0E l r)
| hL (l<:L00) r => Some (h1E (l<:L1<:L1) r)
| hL (l<:L10) r => Some (hL l (0>>1>>r))
| hL (l<:L1) r => Some (hL l (1>>r))
| hL [] r => Some (h1E [] (1>>1>>r))
end.

Definition cfg0 := hL [] ([1;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D E F A B C (@nil Sym).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM41.


Module TM42.
Definition tm := TM_from_str "1RB1RD_0LC---_1LD1LC_1RE0RE_0RF0LA_1RA0RE".
Definition tm' := TM_from_str "1RB0RF_1RC1RE_0LD---_1LE1LD_1RF0RF_0RA0LB".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L10 | L1
.

Inductive Config :=
| h1E(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| h0E(l:list LD)(r:side)
| hA(l:list LD)(r:side)
| h1B(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1E l r => toLC l <* <[1] {{QE}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| h0E l r => toLC l <* <[0] {{QE}}> r
| hA l r => toLC l <* <[] {{QA}}> r
| h1B l r => toLC l <* <[1] {{QB}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| hL l r => toLC l <{{QC}} [1] *> r
end.

Definition f x :=
match x with
| h1E l (0>>r) => Some (hF (l<:L10) r)
| h1E l (1>>r) => Some (h1E (l<:L1) r)
| hF l (0>>r) => Some (hA (l<:L1) r)
| hF l (1>>r) => Some (h0E l r)
| h0E l (0>>r) => Some (hF (l<:L00) r)
| h0E l (1>>r) => Some (hL l (0>>r)) 
| hA l (0>>r) => Some (h1B l r)
| hA l (1>>r) => Some (hD (l<:L1) r)
| h1B l (0>>r) => Some (hL l (0>>r))
| h1B l (1>>r) => None
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => Some (h0E l r)
| hL (l<:L00) r => Some (h1E (l<:L1<:L1) r)
| hL (l<:L10) r => Some (hL l (0>>1>>r))
| hL (l<:L1) r => Some (hL l (1>>r))
| hL [] r => Some (h1E [] (1>>1>>r))
end.

Definition cfg0 := hL [] ([1;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C D E F A <[1;1;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM42.


Module TM43.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1RF0LD_1RA0RE_1RB---_0RD0LC".
Definition tm' := TM_from_str "1RB0LE_1RC0LD_0RD0LB_1RE0RF_1LA0LE_1RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L100 | L10 | L1
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h11C(l:list LD)(r:side)
| h111F(l:list LD)(r:side)
| h10D(l:list LD)(r:side)
| h1A(l:list LD)(r:side)
| hE(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L100::ls => toLC ls <* <[1;0;0]
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1B l r => toLC l <* <[1] {{QB}}> r
| h11C l r => toLC l <* <[1;1] {{QC}}> r
| h111F l r => toLC l <* <[1;1;1] {{QF}}> r
| h10D l r => toLC l <* <[1;0] {{QD}}> r
| h1A l r => toLC l <* <[1] {{QA}}> r
| hE l r => toLC l <* <[] {{QE}}> r
| hL l r => toLC l <{{QA}} [] *> r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h11C l r)
| h1B l (1>>r) => Some (hL l (0>>0>>r))
| h11C l (0>>r) => Some (h111F l r)
| h11C l (1>>r) => Some (h1B (l<:L10) r)
| h111F l (0>>r) => Some (h10D (l<:L1<:L1) r)
| h111F l (1>>r) => Some (h11C (l<:L10) r)
| h10D l (0>>r) => Some (h1A (l<:L10) r)
| h10D l (1>>r) => Some (hE (l<:L100) r)
| h1A l (0>>r) => Some (hL l (0>>1>>r))
| h1A l (1>>r) => Some (hL l (0>>0>>r))
| hE l (0>>r) => Some (h1B l r)
| hE l (1>>r) => None
| hL (l<:L100) r => Some (h1B (l<:L10) r)
| hL (l<:L10) r => Some (hL l (0>>1>>r))
| hL (l<:L1) r => Some (hL l (0>>r))
| hL [] r => Some (h1B [] r)
end.

Definition cfg0 := hL [] ([0;0;0;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (@nil Sym).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E A B D F C <[1;0;1;0].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM43.


Module TM44.
Definition tm := TM_from_str "1LB0LA_1RC0LA_1RF0LD_1RA0RE_1RB---_0RD0LC".
Definition tm' := TM_from_str "1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L100 | L10 | L1
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h11C(l:list LD)(r:side)
| h111F(l:list LD)(r:side)
| h10D(l:list LD)(r:side)
| h1A(l:list LD)(r:side)
| hE(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L100::ls => toLC ls <* <[1;0;0]
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1B l r => toLC l <* <[1] {{QB}}> r
| h11C l r => toLC l <* <[1;1] {{QC}}> r
| h111F l r => toLC l <* <[1;1;1] {{QF}}> r
| h10D l r => toLC l <* <[1;0] {{QD}}> r
| h1A l r => toLC l <* <[1] {{QA}}> r
| hE l r => toLC l <* <[] {{QE}}> r
| hL l r => toLC l <{{QA}} [] *> r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h11C l r)
| h1B l (1>>r) => Some (hL l (0>>0>>r))
| h11C l (0>>r) => Some (h111F l r)
| h11C l (1>>r) => Some (h1B (l<:L10) r)
| h111F l (0>>r) => Some (h10D (l<:L1<:L1) r)
| h111F l (1>>r) => Some (h11C (l<:L10) r)
| h10D l (0>>r) => Some (h1A (l<:L10) r)
| h10D l (1>>r) => Some (hE (l<:L100) r)
| h1A l (0>>r) => Some (hL l (0>>1>>r))
| h1A l (1>>r) => Some (hL l (0>>0>>r))
| hE l (0>>r) => Some (h1B l r)
| hE l (1>>r) => None
| hL (l<:L100) r => Some (h1B (l<:L10) r)
| hL (l<:L10) r => Some (hL l (0>>1>>r))
| hL (l<:L1) r => Some (hL l (0>>r))
| hL [] r => Some (h1B [] r)
end.

Definition cfg0 := hL [] ([0;0;0;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (@nil Sym).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C D A E F <[1;0].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM44.


Module TM45.
Definition tm := TM_from_str "1LB0RD_1LC1LE_1RA0LB_0RF1RA_0RC---_0LA0RA".
Definition tm' := TM_from_str "1LB1LF_1RC0LA_1LA0RD_0RE1RC_0LC0RC_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LH :=
| LH0 | LH1 | LH2.

Inductive LD :=
| L01(a b:nat)
.

Inductive Config :=
| hA(l0:LH)(l:list LD)(k m:nat)(r:side)
| hD(l0:LH)(l:list LD)(k m:nat)(r:side)
| hF(l0:LH)(l:list LD)(k m:nat)(r:side)
| hL(l0:LH)(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lhn:nat.

Fixpoint toLC ls lh :=
match ls with
| L01 a b::ls => toLC ls lh <* <[0;1] <* <[1]^^a <* <[0]^^b
| [] =>
  match lh with
  | LH0 => 0inf <* <[1;0]^^lhn <* <[1;0;0;1]
  | LH1 => 0inf <* <[1;0]^^lhn <* <[1;1;0;1]
  | LH2 => 0inf <* <[1;0]^^lhn <* <[1;0;0;0;0;1]
  end
end.

Definition to_config x :=
match x with
| hA l0 l k m r => toLC (l<:(L01 k (m*3))) l0 {{QA}}> r
| hD l0 l k m r => toLC (l<:(L01 k (1+m*3))) l0 {{QD}}> r
| hF l0 l k m r => toLC (l<:(L01 k (2+m*3))) l0 {{QF}}> r
| hL l0 l r => toLC l l0 <{{QC}} [1;0] *> r
end.

Definition f x :=
match x with
| hA l0 l 0 0 (0>>r) => Some (hL l0 l (1>>r))
| hA l0 l _ 0 (0>>r) => None
| hA l0 l k (S m) (0>>r) => Some (hA l0 (l<:(L01 k (m*3))<:(L01 0 0)) 0 0 r)
| hA l0 l k m (1>>r) => Some (hD l0 l k m r)
| hD l0 l k m (0>>r) => Some (hF l0 l k m r)
| hD l0 l k m (1>>r) => Some (hA l0 (l<:(L01 k (m*3))) 0 0 r)
| hF l0 l 0 0 (0>>r) => Some (hL l0 l (1>>1>>0>>r))
| hF l0 l 1 0 (0>>r) => Some (hL l0 l (0>>1>>1>>0>>r))
| hF l0 l _ 0 (0>>r) => None
| hF l0 l k 1 (0>>r) => Some (hD l0 (l<:(L01 (S k) 0)<:(L01 0 0)) 0 0 r)
| hF l0 l k (S(S m)) (0>>r) => Some (hD l0 (l<:(L01 k (2+m*3))<:(L01 0 0)<:(L01 0 0)) 0 0 r)
| hF l0 l k m (1>>r) => Some (hA l0 l k (S m) r)
| hL l0 (l<:(L01 0 0)) r => Some (hL l0 l (1>>0>>r))
| hL l0 (l<:(L01 1 0)) r => Some (hL l0 l (0>>1>>0>>r))
| hL l0 (l<:(L01 _ 0)) r => None
| hL l0 (l<:(L01 a 1)) r => Some (hF l0 l (S a) 0 r)
| hL l0 (l<:(L01 a (S(S b)))) r => Some (hF l0 (l<:(L01 a b)) 0 0 r)
| hL LH0 [] r => Some (hA LH1 [] 0 0 r)
| hL LH1 [] r => Some (hA LH2 [] 0 0 (1>>0>>r))
| hL LH2 [] r => Some (hA LH0 [] 0 0 (1>>1>>r))
end.

Definition cfg0 := hL LH1 [] ([1;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | LH0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L01 a b => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A C D F 2.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C B D E O.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM45.


Module TM46.
Definition tm := TM_from_str "1RB0LF_0LC0RA_1RA0RD_1RE---_1LA1RC_0LE0LF".
Definition tm' := TM_from_str "1LB1RD_1RC0LF_0LD0RB_1RB0RE_1RA---_0LA0LF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L100 | L10 | L1
.

Inductive Config :=
| h1E(l:list LD)(r:side)
| h1C(l:list LD)(r:side)
| h1A(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| h11B(l:list LD)(r:side)
| h10A(l:list LD)(r:side)
| h101B(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L100::ls => toLC ls <* <[1;0;0]
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1E l r => toLC l <* <[1] {{QE}}> r
| h1C l r => toLC l <* <[1] {{QC}}> r
| h1A l r => toLC l <* <[1] {{QA}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| h11B l r => toLC l <* <[1;1] {{QB}}> r
| h10A l r => toLC l <* <[1;0] {{QA}}> r
| h101B l r => toLC l <* <[1;0;1] {{QB}}> r
| hL l r => toLC l <{{QF}} [] *> r
end.

Definition f x :=
match x with
| h1E l (0>>r) => Some (hL l (0>>1>>r))
| h1E l (1>>r) => Some (h1C (l<:L1) r)
| h1C l (0>>r) => Some (h1A (l<:L1) r)
| h1C l (1>>r) => Some (hD (l<:L10) r)
| h1A l (0>>r) => Some (h11B l r)
| h1A l (1>>r) => Some (hL l (0>>0>>r))
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => None
| h11B l (0>>r) => Some (h1E (l<:L10) r)
| h11B l (1>>r) => Some (h10A (l<:L1) r)
| h10A l (0>>r) => Some (h101B l r)
| h10A l (1>>r) => Some (h11B (l<:L1) r)
| h101B l (0>>r) => Some (h1E (l<:L100) r)
| h101B l (1>>r) => Some (h10A (l<:L10) r)
| hL (l<:L100) r => Some (hL l (0>>1>>0>>r))
| hL (l<:L10) r => Some (h1A (l<:L1) r)
| hL (l<:L1) r => Some (hL l (0>>r))
| hL [] r => Some (h1A [L1;L1] r)
end.

Definition cfg0 := hL [] ([0;0;0;0;1;0;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;0;1;1;1;1;1;0;0].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C D E A F <[1;0;0].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM46.


Module TM47.
Definition tm := TM_from_str "1RB0LA_0RC0RF_0LD1RE_1LA0RB_1RD1RE_1RB---".
Definition tm' := TM_from_str "1LB0RC_1RC0LB_0RE0RD_1RC---_0LA1RF_1RA1RF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L00 | L10 | L1
.

Inductive Config :=
| h11D(l:list LD)(r:side)
| h10B(l:list LD)(r:side)
| h00C(l:list LD)(r:side)
| h100F(l:list LD)(r:side)
| h101B(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| h1001B(l:list LD)(r:side)
| h1010C(l:list LD)(r:side)
| h10F(l:list LD)(r:side)
| h10010C(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L00::ls => toLC ls <* <[0;0]
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h11D l r => toLC l <* <[1;1] {{QD}}> r
| h10B l r => toLC l <* <[1;0] {{QB}}> r
| h00C l r => toLC l <* <[0;0] {{QC}}> r
| h100F l r => toLC l <* <[1;0;0] {{QF}}> r
| h101B l r => toLC l <* <[1;0;1] {{QB}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| h1001B l r => toLC l <* <[1;0;0;1] {{QB}}> r
| h1010C l r => toLC l <* <[1;0;1;0] {{QC}}> r
| h10F l r => toLC l <* <[1;0] {{QF}}> r
| h10010C l r => toLC l <* <[1;0;0;1;0] {{QC}}> r
| hL l r => toLC l <{{QA}} [0;0] *> r
end.

Definition f x :=
match x with
| h11D l (0>>r) => Some (hL l (1>>r))
| h11D l (1>>r) => Some (h10B (l<:L1) r)
| h10B l (0>>r) => Some (h00C (l<:L1) r)
| h10B l (1>>r) => Some (h100F l r)
| h00C l (0>>r) => Some (h101B l r)
| h00C l (1>>r) => Some (h1E (l<:L00) r)
| h100F l (0>>r) => Some (h1001B l r)
| h100F l (1>>r) => None
| h101B l (0>>r) => Some (h1010C l r)
| h101B l (1>>r) => Some (h10F (l<:L10) r)
| h1E l (0>>r) => Some (h11D l r)
| h1E l (1>>r) => Some (h1E (l<:L1) r)
| h1001B l (0>>r) => Some (h10010C l r)
| h1001B l (1>>r) => Some (h10F (l<:L1<:L00) r)
| h1010C l (0>>r) => Some (h11D (l<:L1<:L10) r)
| h1010C l (1>>r) => Some (h1E (l<:L10<:L10) r)
| h10F l (0>>r) => Some (h101B l r)
| h10F l (1>>r) => None
| h10010C l (0>>r) => Some (h11D (l<:L10<:L10) r)
| h10010C l (1>>r) => Some (h1E (l<:L1<:L00<:L10) r)
| hL (l<:L00) r => Some (h11D (l<:L10) r)
| hL (l<:L10) r => Some (hL l (1>>0>>r))
| hL (l<:L1) r => Some (hL l (0>>r))
| hL [] r => Some (h11D [L10] r)
end.

Definition cfg0 := h11D <[L1;L1;L00;L1;L10] (0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Notation w := <[1;0;1;1;1;0].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (w^^2).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C E A F D (w^^2<+<[1;0;1;1;1]<+w^^2).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM47.


Module TM48.
Definition tm := TM_from_str "1RB0RF_1LC1RA_1RA0LD_1RE0LB_0RC---_1RB1RD".
Definition tm' := TM_from_str "1LB1RC_1RC0LE_1RA0RD_1RA1RE_1RF0LA_0RB---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L11010 | L110 | L1
.

Inductive Config :=
| h1110C(l:list LD)(r:side)
| h1101A(l:list LD)(r:side)
| h110C(l:list LD)(r:side)
| h11B(l:list LD)(r:side)
| h11010F(l:list LD)(r:side)
| h11A(l:list LD)(r:side)
| h110101B(l:list LD)(r:side)
| h1D(l:list LD)(r:side)
| h110F(l:list LD)(r:side)
| h11E(l:list LD)(r:side)
| h1101B(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L11010::ls => toLC ls <* <[1;1;0;1;0]
| L110::ls => toLC ls <* <[1;1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1110C l r => toLC l <* <[1;1;1;0] {{QC}}> r
| h1101A l r => toLC l <* <[1;1;0;1] {{QA}}> r
| h110C l r => toLC l <* <[1;1;0] {{QC}}> r
| h11B l r => toLC l <* <[1;1] {{QB}}> r
| h11010F l r => toLC l <* <[1;1;0;1;0] {{QF}}> r
| h11A l r => toLC l <* <[1;1] {{QA}}> r
| h110101B l r => toLC l <* <[1;1;0;1;0;1] {{QB}}> r
| h1D l r => toLC l <* <[1] {{QD}}> r
| h110F l r => toLC l <* <[1;1;0] {{QF}}> r
| h11E l r => toLC l <* <[1;1] {{QE}}> r
| h1101B l r => toLC l <* <[1;1;0;1] {{QB}}> r
| hL l r => toLC l <{{QB}} [0;0] *> r
end.

Definition f x :=
match x with
| h1110C l (0>>r) => Some (h1101A (l<:L1) r)
| h1110C l (1>>r) => Some (h110C (l<:L1<:L1) r)
| h1101A l (0>>r) => Some (h11B (l<:L110) r)
| h1101A l (1>>r) => Some (h11010F l r)
| h110C l (0>>r) => Some (h1101A l r)
| h110C l (1>>r) => Some (h110C (l<:L1) r)
| h11B l (0>>r) => Some (hL l (1>>r))
| h11B l (1>>r) => Some (h11A (l<:L1) r)
| h11010F l (0>>r) => Some (h110101B l r)
| h11010F l (1>>r) => Some (h1D (l<:L11010) r)
| h11A l (0>>r) => Some (h11B (l<:L1) r)
| h11A l (1>>r) => Some (h110F l r)
| h110101B l (0>>r) => Some (h110C (l<:L110<:L1) r)
| h110101B l (1>>r) => Some (h11A (l<:L11010) r)
| h1D l (0>>r) => Some (h11E l r)
| h1D l (1>>r) => Some (h11B l r)
| h110F l (0>>r) => Some (h1101B l r)
| h110F l (1>>r) => Some (h1D (l<:L110) r)
| h11E l (0>>r) => Some (h110C l r)
| h11E l (1>>r) => None
| h1101B l (0>>r) => Some (h110C (l<:L1<:L1) r)
| h1101B l (1>>r) => Some (h11A (l<:L110) r)
| hL (l<:L11010) r => Some (h1110C l (1>>0>>0>>r))
| hL (l<:L110) r => Some (hL l (1>>0>>0>>r))
| hL (l<:L1) r => Some (hL l (1>>r))
| hL [] r => Some (h1110C [] r)
end.

Definition cfg0 := h1110C <[] ([1;0;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (@nil Sym).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C A B E F D <[1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM48.


Module TM49.
Definition tm := TM_from_str "1RB0RF_1LC1RA_1RA0LD_1RE0LB_0RC---_1RB1RD".
Definition tm' := TM_from_str "1RB0LD_1RC0RE_1LA1RB_1RF0LC_1RC1RD_0RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L11010 | L110 | L1
.

Inductive Config :=
| h1110C(l:list LD)(r:side)
| h1101A(l:list LD)(r:side)
| h110C(l:list LD)(r:side)
| h11B(l:list LD)(r:side)
| h11010F(l:list LD)(r:side)
| h11A(l:list LD)(r:side)
| h110101B(l:list LD)(r:side)
| h1D(l:list LD)(r:side)
| h110F(l:list LD)(r:side)
| h11E(l:list LD)(r:side)
| h1101B(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L11010::ls => toLC ls <* <[1;1;0;1;0]
| L110::ls => toLC ls <* <[1;1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1110C l r => toLC l <* <[1;1;1;0] {{QC}}> r
| h1101A l r => toLC l <* <[1;1;0;1] {{QA}}> r
| h110C l r => toLC l <* <[1;1;0] {{QC}}> r
| h11B l r => toLC l <* <[1;1] {{QB}}> r
| h11010F l r => toLC l <* <[1;1;0;1;0] {{QF}}> r
| h11A l r => toLC l <* <[1;1] {{QA}}> r
| h110101B l r => toLC l <* <[1;1;0;1;0;1] {{QB}}> r
| h1D l r => toLC l <* <[1] {{QD}}> r
| h110F l r => toLC l <* <[1;1;0] {{QF}}> r
| h11E l r => toLC l <* <[1;1] {{QE}}> r
| h1101B l r => toLC l <* <[1;1;0;1] {{QB}}> r
| hL l r => toLC l <{{QB}} [0;0] *> r
end.

Definition f x :=
match x with
| h1110C l (0>>r) => Some (h1101A (l<:L1) r)
| h1110C l (1>>r) => Some (h110C (l<:L1<:L1) r)
| h1101A l (0>>r) => Some (h11B (l<:L110) r)
| h1101A l (1>>r) => Some (h11010F l r)
| h110C l (0>>r) => Some (h1101A l r)
| h110C l (1>>r) => Some (h110C (l<:L1) r)
| h11B l (0>>r) => Some (hL l (1>>r))
| h11B l (1>>r) => Some (h11A (l<:L1) r)
| h11010F l (0>>r) => Some (h110101B l r)
| h11010F l (1>>r) => Some (h1D (l<:L11010) r)
| h11A l (0>>r) => Some (h11B (l<:L1) r)
| h11A l (1>>r) => Some (h110F l r)
| h110101B l (0>>r) => Some (h110C (l<:L110<:L1) r)
| h110101B l (1>>r) => Some (h11A (l<:L11010) r)
| h1D l (0>>r) => Some (h11E l r)
| h1D l (1>>r) => Some (h11B l r)
| h110F l (0>>r) => Some (h1101B l r)
| h110F l (1>>r) => Some (h1D (l<:L110) r)
| h11E l (0>>r) => Some (h110C l r)
| h11E l (1>>r) => None
| h1101B l (0>>r) => Some (h110C (l<:L1<:L1) r)
| h1101B l (1>>r) => Some (h11A (l<:L110) r)
| hL (l<:L11010) r => Some (h1110C l (1>>0>>0>>r))
| hL (l<:L110) r => Some (hL l (1>>0>>0>>r))
| hL (l<:L1) r => Some (hL l (1>>r))
| hL [] r => Some (h1110C [] r)
end.

Definition cfg0 := h1110C <[] ([1;0;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (@nil Sym).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C A D F E <[1;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM49.


Module TM50.
Definition tm := TM_from_str "1RB0RF_1LC1RA_1RA0LD_1RE0LB_0RC---_1RB1RD".
Definition tm' := TM_from_str "1RB0LE_0RC---_1RD0LA_1RE0RF_1LC1RD_1RE1RA".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L11010 | L110 | L1
.

Inductive Config :=
| h1110C(l:list LD)(r:side)
| h1101A(l:list LD)(r:side)
| h110C(l:list LD)(r:side)
| h11B(l:list LD)(r:side)
| h11010F(l:list LD)(r:side)
| h11A(l:list LD)(r:side)
| h110101B(l:list LD)(r:side)
| h1D(l:list LD)(r:side)
| h110F(l:list LD)(r:side)
| h11E(l:list LD)(r:side)
| h1101B(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L11010::ls => toLC ls <* <[1;1;0;1;0]
| L110::ls => toLC ls <* <[1;1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h1110C l r => toLC l <* <[1;1;1;0] {{QC}}> r
| h1101A l r => toLC l <* <[1;1;0;1] {{QA}}> r
| h110C l r => toLC l <* <[1;1;0] {{QC}}> r
| h11B l r => toLC l <* <[1;1] {{QB}}> r
| h11010F l r => toLC l <* <[1;1;0;1;0] {{QF}}> r
| h11A l r => toLC l <* <[1;1] {{QA}}> r
| h110101B l r => toLC l <* <[1;1;0;1;0;1] {{QB}}> r
| h1D l r => toLC l <* <[1] {{QD}}> r
| h110F l r => toLC l <* <[1;1;0] {{QF}}> r
| h11E l r => toLC l <* <[1;1] {{QE}}> r
| h1101B l r => toLC l <* <[1;1;0;1] {{QB}}> r
| hL l r => toLC l <{{QB}} [0;0] *> r
end.

Definition f x :=
match x with
| h1110C l (0>>r) => Some (h1101A (l<:L1) r)
| h1110C l (1>>r) => Some (h110C (l<:L1<:L1) r)
| h1101A l (0>>r) => Some (h11B (l<:L110) r)
| h1101A l (1>>r) => Some (h11010F l r)
| h110C l (0>>r) => Some (h1101A l r)
| h110C l (1>>r) => Some (h110C (l<:L1) r)
| h11B l (0>>r) => Some (hL l (1>>r))
| h11B l (1>>r) => Some (h11A (l<:L1) r)
| h11010F l (0>>r) => Some (h110101B l r)
| h11010F l (1>>r) => Some (h1D (l<:L11010) r)
| h11A l (0>>r) => Some (h11B (l<:L1) r)
| h11A l (1>>r) => Some (h110F l r)
| h110101B l (0>>r) => Some (h110C (l<:L110<:L1) r)
| h110101B l (1>>r) => Some (h11A (l<:L11010) r)
| h1D l (0>>r) => Some (h11E l r)
| h1D l (1>>r) => Some (h11B l r)
| h110F l (0>>r) => Some (h1101B l r)
| h110F l (1>>r) => Some (h1D (l<:L110) r)
| h11E l (0>>r) => Some (h110C l r)
| h11E l (1>>r) => None
| h1101B l (0>>r) => Some (h110C (l<:L1<:L1) r)
| h1101B l (1>>r) => Some (h11A (l<:L110) r)
| hL (l<:L11010) r => Some (h1110C l (1>>0>>0>>r))
| hL (l<:L110) r => Some (hL l (1>>0>>0>>r))
| hL (l<:L1) r => Some (hL l (1>>r))
| hL [] r => Some (h1110C [] r)
end.

Definition cfg0 := h1110C <[] ([1;0;0;1;1;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;1].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D E C A B F (@nil Sym).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM50.


Module TM51.
Definition tm := TM_from_str "1RB0LA_0LC0RC_1RD1LA_1LA1RE_0RD0RF_1RC---".
Definition tm' := TM_from_str "1RB1LC_1LC1RE_1RD0LC_0LA0RA_0RB0RF_1RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L10 | L1
.

Inductive Config :=
| h101D(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| h10D(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| h10C(l:list LD)(r:side)
| h1C(l:list LD)(r:side)
| h1D(l:list LD)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| L10::ls => toLC ls <* <[1;0]
| L1::ls => toLC ls <* <[1]
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| h101D l r => toLC l <* <[1;0;1] {{QD}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| h10D l r => toLC l <* <[1;0] {{QD}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| h10C l r => toLC l <* <[1;0] {{QC}}> r
| h1C l r => toLC l <* <[1] {{QC}}> r
| h1D l r => toLC l <* <[1] {{QD}}> r
| hL l r => toLC l <{{QA}} [0] *> r
end.

Definition f x :=
match x with
| h101D l (0>>r) => Some (hL l (1>>0>>1>>r))
| h101D l (1>>r) => Some (h1E (l<:L10<:L1) r)
| h1E l (0>>r) => Some (h10D l r)
| h1E l (1>>r) => Some (hF (l<:L10) r)
| h10D l (0>>r) => Some (h10C (l<:L1) r)
| h10D l (1>>r) => Some (h1E (l<:L10) r)
| hF l (0>>r) => Some (h1C l r)
| hF l (1>>r) => None
| h10C l (0>>r) => Some (h1D (l<:L10) r)
| h10C l (1>>r) => Some (h10C (l<:L1) r)
| h1C l (0>>r) => Some (h1D (l<:L1) r)
| h1C l (1>>r) => Some (hL l (1>>r))
| h1D l (0>>r) => Some (hL l (1>>r))
| h1D l (1>>r) => Some (h1E (l<:L1) r)
| hL (l<:L10) r => Some (hL l (1>>0>>r))
| hL (l<:L1) r => Some (hL l (0>>r))
| hL [] r => Some (h101D [] r)
end.

Definition cfg0 := h101D <[] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A C D E F (@nil Sym).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C A B E F <[1;0;1;1].
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM51.


Module TM52.
Definition tm := TM_from_str "1RB0LD_0RC0RE_1RD0RC_1LA0LD_1RF---_0RB0RA".
Definition tm' := TM_from_str "1RB0RA_1LC0LB_1RD0LB_0RA0RE_1RF---_0RD0RC".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LH :=
| LH0
.

Inductive LD :=
| L1(a:nat)
.

Inductive Config :=
| hE(l0:LH)(l:list LD)(r:side)
| h1F(l0:LH)(l:list LD)(r:side)
| h10B(l0:LH)(l:list LD)(r:side)
| hA(l0:LH)(l:list LD)(r:side)
| h1B(l0:LH)(l:list LD)(r:side)
| h1D(l0:LH)(l:list LD)(r:side)
| hC(l0:LH)(l:list LD)(m:nat)(r:side)
| hL(l0:LH)(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lha:nat.

Fixpoint toLC ls :=
match ls with
| L1 a::ls => toLC ls <* <[1] <* <[0]^^a
| [] => 0inf <* <[1;0]^^lha
end.

Definition to_config x :=
match x with
| hE l0 l r => toLC l {{QE}}> r
| h1F l0 l r => toLC l <* <[1] {{QF}}> r
| h10B l0 l r => toLC l <* <[1;0] {{QB}}> r
| hA l0 l r => toLC l {{QA}}> r
| h1B l0 l r => toLC l <* <[1] {{QB}}> r
| h1D l0 l r => toLC l <* <[1] {{QD}}> r
| hC l0 l m r => toLC l <* <[1] <* <[0]^^m {{QC}}> r
| hL l0 l r => toLC l <{{QD}} r
end.

Definition f x :=
match x with
| hE l0 l (0>>r) => Some (h1F l0 l r)
| hE l0 l (1>>r) => None
| h1F l0 l (0>>r) => Some (h10B l0 l r)
| h1F l0 l (1>>r) => Some (hA l0 (l<:(L1 1)) r)
| h10B l0 l (0>>r) => Some (hC l0 l 2 r)
| h10B l0 l (1>>r) => Some (hE l0 (l<:(L1 2)) r)
| hA l0 l (0>>r) => Some (h1B l0 l r)
| hA l0 l (1>>r) => Some (hL l0 l (0>>r))
| h1B l0 l (0>>r) => Some (hC l0 l 1 r)
| h1B l0 l (1>>r) => Some (hE l0 (l<:(L1 1)) r)
| h1D l0 l (0>>r) => Some (hL l0 l (0>>1>>r))
| h1D l0 l (1>>r) => Some (hL l0 l (0>>0>>r))
| hC l0 l m (0>>r) => Some (h1D l0 (l<:(L1 m)) r)
| hC l0 l m (1>>r) => Some (hC l0 l (S m) r)
| hL l0 (l<:(L1 0)) r => Some (hL l0 l (0>>r))
| hL l0 (l<:(L1 1)) r => Some (hL l0 l (0>>1>>r))
| hL l0 (l<:(L1 (S(S m)))) r => Some (h1B l0 (l<:(L1 m)) (1>>r))
| hL _ [] r => Some (hE LH0 [L1 1] r)
end.

Definition cfg0 := hL LH0 [] ([0;1;0;0;1;0;1;0;1;0;1;0]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | LH0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 a => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F 2.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C D A B E F 4.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM52.


Module TM53.
Definition tm := TM_from_str "1RB0LD_0RC0RE_1RD0RC_1LA0LD_1RF---_0RB0RA".
Definition tm' := TM_from_str "1LB0LA_1RC0LA_0RF0RD_1RE---_0RC0RB_1RA0RF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LH :=
| LH0
.

Inductive LD :=
| L1(a:nat)
.

Inductive Config :=
| hE(l0:LH)(l:list LD)(r:side)
| h1F(l0:LH)(l:list LD)(r:side)
| h10B(l0:LH)(l:list LD)(r:side)
| hA(l0:LH)(l:list LD)(r:side)
| h1B(l0:LH)(l:list LD)(r:side)
| h1D(l0:LH)(l:list LD)(r:side)
| hC(l0:LH)(l:list LD)(m:nat)(r:side)
| hL(l0:LH)(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lha:nat.

Fixpoint toLC ls :=
match ls with
| L1 a::ls => toLC ls <* <[1] <* <[0]^^a
| [] => 0inf <* <[1;0]^^lha
end.

Definition to_config x :=
match x with
| hE l0 l r => toLC l {{QE}}> r
| h1F l0 l r => toLC l <* <[1] {{QF}}> r
| h10B l0 l r => toLC l <* <[1;0] {{QB}}> r
| hA l0 l r => toLC l {{QA}}> r
| h1B l0 l r => toLC l <* <[1] {{QB}}> r
| h1D l0 l r => toLC l <* <[1] {{QD}}> r
| hC l0 l m r => toLC l <* <[1] <* <[0]^^m {{QC}}> r
| hL l0 l r => toLC l <{{QD}} r
end.

Definition f x :=
match x with
| hE l0 l (0>>r) => Some (h1F l0 l r)
| hE l0 l (1>>r) => None
| h1F l0 l (0>>r) => Some (h10B l0 l r)
| h1F l0 l (1>>r) => Some (hA l0 (l<:(L1 1)) r)
| h10B l0 l (0>>r) => Some (hC l0 l 2 r)
| h10B l0 l (1>>r) => Some (hE l0 (l<:(L1 2)) r)
| hA l0 l (0>>r) => Some (h1B l0 l r)
| hA l0 l (1>>r) => Some (hL l0 l (0>>r))
| h1B l0 l (0>>r) => Some (hC l0 l 1 r)
| h1B l0 l (1>>r) => Some (hE l0 (l<:(L1 1)) r)
| h1D l0 l (0>>r) => Some (hL l0 l (0>>1>>r))
| h1D l0 l (1>>r) => Some (hL l0 l (0>>0>>r))
| hC l0 l m (0>>r) => Some (h1D l0 (l<:(L1 m)) r)
| hC l0 l m (1>>r) => Some (hC l0 l (S m) r)
| hL l0 (l<:(L1 0)) r => Some (hL l0 l (0>>r))
| hL l0 (l<:(L1 1)) r => Some (hL l0 l (0>>1>>r))
| hL l0 (l<:(L1 (S(S m)))) r => Some (h1B l0 (l<:(L1 m)) (1>>r))
| hL _ [] r => Some (hE LH0 [L1 1] r)
end.

Definition cfg0 := hL LH0 [] ([0;1;0;0;1;0;1;0;1;0;1;0]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | LH0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 a => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F 2.
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C F A D E O.
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM53.


Module TM54.
Definition tm := TM_from_str "1RB0RA_0RC0RF_1RD1LD_1LE---_1LF1LE_1RA0LE".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_0RD0RA_1RE1LE_1LF---_1LA1LF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1(n:nat)
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h10C(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| hA(l:list LD)(m:nat)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L1 n)::ls => toLC ls <* <[1] <* <[0]^^n
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hA l m r => toLC l <* <[1] <* <[0]^^m {{QA}}> r
| h1B l r => toLC l <* <[1] {{QB}}> r
| h10C l r => toLC l <* <[1;0] {{QC}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| hL l r => toLC l <{{QE}} [] *> r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h10C l r)
| h1B l (1>>r) => Some (hF (l<:(L1 1)) r)
| h10C l (0>>r) => Some (hD (l<:(L1 1)<:(L1 0)) r)
| h10C l (1>>r) => Some (hL l (1>>1>>1>>r))
| hF l (0>>r) => Some (hA l 0 r)
| hF l (1>>r) => Some (hL l (0>>r))
| hD l (0>>r) => Some (hL l (1>>r))
| hD l (1>>r) => None
| hA l m (0>>r) => Some (h1B (l<:(L1 m)) r)
| hA l m (1>>r) => Some (hA l (S m) r)
| hL (l<:(L1 (S(S m)))) r => Some (hA (l<:(L1 m)) 1 r)
| hL (l<:(L1 1)) r => Some (hL l (0>>1>>r))
| hL (l<:(L1 0)) r => Some (hL l (1>>r))
| hL [] r => Some (hA [] 1 r)
end.

Definition cfg0 := hL <[] ([1;0;1;1;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 _ => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F <[1;0;1;0;1;0;1;0].
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C D E F A (@nil Sym).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM54.


Module TM55.
Definition tm := TM_from_str "1RB0RA_0RC0RF_1RD1LD_1RE---_1LF1LE_1RA0LE".
Definition tm' := TM_from_str "1RB1LB_1RC---_1LD1LC_1RE0LC_1RF0RE_0RA0RD".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1(n:nat)
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h10C(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| hA(l:list LD)(m:nat)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L1 n)::ls => toLC ls <* <[1] <* <[0]^^n
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hA l m r => toLC l <* <[1] <* <[0]^^m {{QA}}> r
| h1B l r => toLC l <* <[1] {{QB}}> r
| h10C l r => toLC l <* <[1;0] {{QC}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| hL l r => toLC l <{{QE}} [] *> r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h10C l r)
| h1B l (1>>r) => Some (hF (l<:(L1 1)) r)
| h10C l (0>>r) => Some (hD (l<:(L1 1)<:(L1 0)) r)
| h10C l (1>>r) => Some (hL l (1>>1>>1>>r))
| hF l (0>>r) => Some (hA l 0 r)
| hF l (1>>r) => Some (hL l (0>>r))
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => None
| h1E l (0>>r) => Some (hL l (0>>1>>r))
| h1E l (1>>r) => Some (hL l (1>>1>>r))
| hA l m (0>>r) => Some (h1B (l<:(L1 m)) r)
| hA l m (1>>r) => Some (hA l (S m) r)
| hL (l<:(L1 (S(S m)))) r => Some (hA (l<:(L1 m)) 1 r)
| hL (l<:(L1 1)) r => Some (hL l (0>>1>>r))
| hL (l<:(L1 0)) r => Some (hL l (1>>r))
| hL [] r => Some (hA [] 1 r)
end.

Definition cfg0 := hL <[] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 _ => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (<[1;0]^^8).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E F A B C D (@nil Sym).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM55.


Module TM56.
Definition tm := TM_from_str "1RB0RA_0RC0RF_1RD1LD_1RE---_1LF1LE_1RA0LE".
Definition tm' := TM_from_str "1LB1LA_1RC0LA_1RD0RC_0RE0RB_1RF1LF_1RA---".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1(n:nat)
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h10C(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| hA(l:list LD)(m:nat)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L1 n)::ls => toLC ls <* <[1] <* <[0]^^n
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hA l m r => toLC l <* <[1] <* <[0]^^m {{QA}}> r
| h1B l r => toLC l <* <[1] {{QB}}> r
| h10C l r => toLC l <* <[1;0] {{QC}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| hL l r => toLC l <{{QE}} [] *> r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h10C l r)
| h1B l (1>>r) => Some (hF (l<:(L1 1)) r)
| h10C l (0>>r) => Some (hD (l<:(L1 1)<:(L1 0)) r)
| h10C l (1>>r) => Some (hL l (1>>1>>1>>r))
| hF l (0>>r) => Some (hA l 0 r)
| hF l (1>>r) => Some (hL l (0>>r))
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => None
| h1E l (0>>r) => Some (hL l (0>>1>>r))
| h1E l (1>>r) => Some (hL l (1>>1>>r))
| hA l m (0>>r) => Some (h1B (l<:(L1 m)) r)
| hA l m (1>>r) => Some (hA l (S m) r)
| hL (l<:(L1 (S(S m)))) r => Some (hA (l<:(L1 m)) 1 r)
| hL (l<:(L1 1)) r => Some (hL l (0>>1>>r))
| hL (l<:(L1 0)) r => Some (hL l (1>>r))
| hL [] r => Some (hA [] 1 r)
end.

Definition cfg0 := hL <[] ([1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 _ => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (<[1;0]^^8).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C D E F A B (<[1;0]^^2).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM56.


Module TM57.
Definition tm := TM_from_str "1RB---_1LC1LB_1RD0LB_1RE0RD_0RF0RC_1RA1LA".
Definition tm' := TM_from_str "1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1(n:nat)
.

Inductive Config :=
| h1B(l:list LD)(r:side)
| h10C(l:list LD)(r:side)
| hF(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| hA(l:list LD)(m:nat)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L1 n)::ls => toLC ls <* <[1] <* <[0]^^n
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hA l m r => toLC l <* <[1] <* <[0]^^m {{QA}}> r
| h1B l r => toLC l <* <[1] {{QB}}> r
| h10C l r => toLC l <* <[1;0] {{QC}}> r
| hF l r => toLC l <* <[] {{QF}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| hL l r => toLC l <{{QE}} [] *> r
end.

Definition f x :=
match x with
| h1B l (0>>r) => Some (h10C l r)
| h1B l (1>>r) => Some (hF (l<:(L1 1)) r)
| h10C l (0>>r) => Some (hD (l<:(L1 1)<:(L1 0)) r)
| h10C l (1>>r) => Some (hL l (1>>1>>1>>r))
| hF l (0>>r) => Some (hA l 0 r)
| hF l (1>>r) => Some (hL l (0>>r))
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => None
| h1E l (0>>r) => Some (hL l (0>>1>>r))
| h1E l (1>>r) => Some (hL l (1>>1>>r))
| hA l m (0>>r) => Some (h1B (l<:(L1 m)) r)
| hA l m (1>>r) => Some (hA l (S m) r)
| hL (l<:(L1 (S(S m)))) r => Some (hA (l<:(L1 m)) 1 r)
| hL (l<:(L1 1)) r => Some (hL l (0>>1>>r))
| hL (l<:(L1 0)) r => Some (hL l (1>>r))
| hL [] r => Some (hA [] 1 r)
end.

Definition cfg0 := hL <[] ([1;0;1;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 _ => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D E F A B C (<[1;0]^^2).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 B C D E F A (<[1;0]^^0).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM57.


Module TM58.
Definition tm := TM_from_str "1RB0LF_1RC0RB_1RD0RA_1RE1LF_1LA---_1LA1LF".
Definition tm' := TM_from_str "1RB1LD_1LC---_1RE0LD_1LC1LD_1RF0RE_1RA0RC".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1(n:nat)
.

Inductive Config :=
| h1C(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| hA(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| hB(l:list LD)(m:nat)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L1 n)::ls => toLC ls <* <[1] <* <[0]^^n
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hB l m r => toLC l <* <[1] <* <[0]^^m {{QB}}> r
| h1C l r => toLC l <* <[1] {{QC}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| hA l r => toLC l <* <[] {{QA}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| hL l r => toLC l <{{QF}} [] *> r
end.

Definition f x :=
match x with
| h1C l (0>>r) => Some (hD (l<:(L1 0)<:(L1 0)) r)
| h1C l (1>>r) => Some (hA (l<:(L1 1)) r)
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => Some (hL l (1>>r))
| hA l (0>>r) => Some (hB l 0 r)
| hA l (1>>r) => Some (hL l (0>>r))
| h1E l (0>>r) => Some (hL l (0>>1>>r))
| h1E l (1>>r) => None
| hB l m (0>>r) => Some (h1C (l<:(L1 m)) r)
| hB l m (1>>r) => Some (hB l (S m) r)
| hL (l<:(L1 (S(S m)))) r => Some (hB (l<:(L1 m)) 1 r)
| hL (l<:(L1 1)) r => Some (hL l (0>>1>>r))
| hL (l<:(L1 0)) r => Some (hL l (1>>r))
| hL [] r => Some (hB [] 1 r)
end.

Definition cfg0 := hL <[] ([1;1;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 _ => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 A B C D E F (<[1;0]^^0).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 C E F A B D (<[1;0]^^2).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM58.


Module TM59.
Definition tm := TM_from_str "1RB0RA_1RC0RE_1RD1LF_1LE---_1RA0LF_1LE1LF".
Definition tm' := TM_from_str "1RB0RD_1RC1LE_1LD---_1RF0LE_1LD1LE_1RA0RF".

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Inductive LD :=
| L1(n:nat)
.

Inductive Config :=
| h1C(l:list LD)(r:side)
| hD(l:list LD)(r:side)
| hA(l:list LD)(r:side)
| h1E(l:list LD)(r:side)
| hB(l:list LD)(m:nat)(r:side)
| hL(l:list LD)(r:side)
.

Section to_config_sec.
Hypothesis QA QB QC QD QE QF:Q.
Hypothesis lh:list sym.

Fixpoint toLC ls :=
match ls with
| (L1 n)::ls => toLC ls <* <[1] <* <[0]^^n
| [] => 0inf <* lh
end.

Definition to_config x :=
match x with
| hB l m r => toLC l <* <[1] <* <[0]^^m {{QB}}> r
| h1C l r => toLC l <* <[1] {{QC}}> r
| hD l r => toLC l <* <[] {{QD}}> r
| hA l r => toLC l <* <[] {{QA}}> r
| h1E l r => toLC l <* <[1] {{QE}}> r
| hL l r => toLC l <{{QF}} [] *> r
end.

Definition f x :=
match x with
| h1C l (0>>r) => Some (hD (l<:(L1 0)<:(L1 0)) r)
| h1C l (1>>r) => Some (hA (l<:(L1 1)) r)
| hD l (0>>r) => Some (h1E l r)
| hD l (1>>r) => Some (hL l (1>>r))
| hA l (0>>r) => Some (hB l 0 r)
| hA l (1>>r) => Some (hL l (0>>r))
| h1E l (0>>r) => Some (hL l (0>>1>>r))
| h1E l (1>>r) => None
| hB l m (0>>r) => Some (h1C (l<:(L1 m)) r)
| hB l m (1>>r) => Some (hB l (S m) r)
| hL (l<:(L1 (S(S m)))) r => Some (hB (l<:(L1 m)) 1 r)
| hL (l<:(L1 1)) r => Some (hL l (0>>1>>r))
| hL (l<:(L1 0)) r => Some (hL l (1>>r))
| hL [] r => Some (hB [] 1 r)
end.

Definition cfg0 := hL <[] ([1;0;1;0;1;0;1;1;0;1]*>0inf).

End to_config_sec.

Ltac des_nat :=
match goal with
| |- context[match ?a with | O => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | [] => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | _ >> _ => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | 0 => _ | _ => _ end] =>
  destruct a
| |- context[match ?a with | L1 _ => _ | _ => _ end] =>
  destruct a
end.

Ltac solve_v1 p0 p1 p2 p3 p4 p5 p6 :=
  erewrite <-(halts_iff _ _ _ f (to_config p0 p1 p2 p3 p4 p5 p6) (fun _=>True)); trivial;
  [ apply halts_evstep_iff; esx | ];
  intros [] _;
  unfold f,to_config;
  repeat des_nat;
  try (split; trivial);
  cbn[toLC lpow];
  try solve[esx].

Lemma eqv1:
  halts tm c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 E A B C D F (<[1;0]^^4).
Qed.

Lemma eqv2:
  halts tm' c0 <-> iter_halts f cfg0.
Proof.
  solve_v1 D F A B C E (<[1;0]^^0).
Qed.

Lemma eqv: halts tm c0 <-> halts tm' c0.
Proof.
  rewrite eqv1,eqv2; tauto.
Qed.

End TM59.


