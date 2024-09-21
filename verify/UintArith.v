From Coq Require Uint63.
From Coq Require Import Lia.


Module N'.
Import Uint63.
Import ZArith.
Open Scope uint63_scope.

Inductive N' :=
| N'uint(a:int)
| N'N(a:N)
.

Definition N'toN(a:N'):N :=
match a with
| N'uint a0 => Z.to_N (to_Z a0)
| N'N a0 => a0
end.

Definition N'addN(a b:N'):N' :=
  N'N ((N'toN a)+(N'toN b))%N.

Definition N'subN(a b:N'):N' :=
  N'N ((N'toN a)-(N'toN b))%N.

Definition N'divN(a b:N'):N' :=
  N'N ((N'toN a)/(N'toN b))%N.

Definition N'modN(a b:N'):N' :=
  N'N ((N'toN a) mod (N'toN b))%N.

Definition N'minN(a b:N'):N' :=
  N'N (N.min (N'toN a) (N'toN b)).

Definition N'add(a b:N'):N':=
match a,b with
| N'uint a0,N'uint b0 =>
  match a0 +c b0 with
  | C1 x => N'addN a b
  | C0 x => N'uint x
  end
| _,_ => N'addN a b
end.

Definition N'sub(a b:N'):N':=
match a,b with
| N'uint a0,N'uint b0 =>
  match a0 -c b0 with
  | C1 x => N'uint 0
  | C0 x => N'uint x
  end
| _,_ => N'subN a b
end.

Definition N'div(a b:N'):N':=
match a,b with
| N'uint a0,N'uint b0 => N'uint (a0/b0)
| _,_ => N'divN a b
end.

Definition N'mod(a b:N'):N':=
match a,b with
| N'uint a0,N'uint b0 => N'uint (a0 mod b0)
| _,_ => N'modN a b
end.

Definition N'min(a b:N'):N':=
match a,b with
| N'uint a0,N'uint b0 => N'uint (if a0 <? b0 then a0 else b0)
| _,_ => N'minN a b
end.

Definition N'OS(a:N'):option N' :=
match a with
| N'uint a0 =>
  if a0=?0 then None else Some (N'uint (a0-1))
| N'N a0 =>
  if (a0=?0)%N then None else Some (N'N (N.pred a0))
end.

Definition N'to_nat(a:N'):nat :=
match a with
| N'uint a0 => Z.to_nat (to_Z a0)
| N'N a0 => N.to_nat a0
end.

Definition N'to_nat3(a:N'*N'*N'):nat*nat*nat :=
let '(a0,a1,a2):=a in
(N'to_nat a0,
N'to_nat a1,
N'to_nat a2).

Definition N'to_onat3(a:option (N'*N'*N')):option (nat*nat*nat) :=
match a with
| None => None
| Some a0 => Some (N'to_nat3 a0)
end.

Lemma N'addN_inj a b:
  N'to_nat (N'addN a b) = ((N'to_nat a)+(N'to_nat b))%nat.
Proof.
  unfold N'addN.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'toN];
  cbn[N'to_nat]; lia.
Qed.

Lemma N'subN_inj a b:
  N'to_nat (N'subN a b) = ((N'to_nat a)-(N'to_nat b))%nat.
Proof.
  unfold N'subN.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'toN];
  cbn[N'to_nat]; lia.
Qed.

Lemma N'divN_inj a b:
  N'to_nat (N'divN a b) = ((N'to_nat a)/(N'to_nat b))%nat.
Proof.
  unfold N'divN.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'toN];
  cbn[N'to_nat];
  rewrite Nnat.N2Nat.inj_div;
  repeat rewrite Z_N_nat;
  reflexivity.
Qed.

Lemma N'modN_inj a b:
  N'to_nat (N'modN a b) = ((N'to_nat a) mod (N'to_nat b))%nat.
Proof.
  unfold N'modN.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'toN];
  cbn[N'to_nat];
  rewrite Nnat.N2Nat.inj_mod;
  repeat rewrite Z_N_nat;
  reflexivity.
Qed.

Lemma N'minN_inj a b:
  N'to_nat (N'minN a b) = (min (N'to_nat a) (N'to_nat b)).
Proof.
  unfold N'minN.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'toN];
  cbn[N'to_nat];
  rewrite Nnat.N2Nat.inj_min;
  repeat rewrite Z_N_nat;
  reflexivity.
Qed.

Lemma N'add_inj a b:
  N'to_nat (N'add a b) = ((N'to_nat a)+(N'to_nat b))%nat.
Proof.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'add];
  try apply N'addN_inj.
  pose proof (addc_spec a b) as H.
  destruct (a +c b) as [x|x] eqn:E.
  2: apply N'addN_inj.
  cbn[N'to_nat].
  unfold interp_carry in H.
  pose proof (to_Z_bounded a).
  pose proof (to_Z_bounded b).
  lia.
Qed.

Lemma N'sub_inj a b:
  N'to_nat (N'sub a b) = ((N'to_nat a)-(N'to_nat b))%nat.
Proof.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'sub];
  try apply N'subN_inj.
  pose proof (subc_spec a b) as H.
  destruct (a -c b) as [x|x] eqn:E.
  - cbn[N'to_nat].
    unfold interp_carry in H.
    pose proof (to_Z_bounded a).
    pose proof (to_Z_bounded b).
    lia.
  - cbn[N'to_nat].
    unfold interp_carry in H.
    pose proof (to_Z_bounded x).
    change (to_Z 0) with Z0.
    lia.
Qed.

Lemma N'div_inj a b:
  N'to_nat (N'div a b) = ((N'to_nat a)/(N'to_nat b))%nat.
Proof.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'div];
  try apply N'divN_inj.
  cbn[N'to_nat].
  rewrite div_spec.
  pose proof (to_Z_bounded a).
  pose proof (to_Z_bounded b).
  apply Z2Nat.inj_div; lia.
Qed.

Lemma N'mod_inj a b:
  N'to_nat (N'mod a b) = ((N'to_nat a) mod (N'to_nat b))%nat.
Proof.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'mod];
  try apply N'modN_inj.
  cbn[N'to_nat].
  rewrite mod_spec.
  pose proof (to_Z_bounded a).
  pose proof (to_Z_bounded b).
  apply Z2Nat.inj_mod; lia.
Qed.

Lemma N'min_inj a b:
  N'to_nat (N'min a b) = (min (N'to_nat a) (N'to_nat b)).
Proof.
  destruct a as [a|a];
  destruct b as [b|b];
  cbn[N'min];
  try apply N'minN_inj.
  cbn[N'to_nat].
  destruct (ltbP a b) as [E|E]; lia.
Qed.

Lemma N'OS_spec a:
match N'OS a with
| None => N'to_nat a = O
| Some a' => N'to_nat a = S (N'to_nat a')
end.
Proof.
  destruct a as [a|a]; cbn[N'OS].
  - destruct (a =? 0) eqn:E.
    + rewrite eqb_spec in E.
      rewrite E.
      reflexivity.
    + rewrite eqb_false_spec in E.
      cbn[N'to_nat].
      rewrite sub_spec.
      change (to_Z 1) with (1%Z).
      pose proof (to_Z_bounded a).
      assert ((φ a) <> 0%Z). {
        intro H0.
        pose proof (to_Z_inj a 0 H0) as H1.
        congruence.
      }
      rewrite Z.mod_small; lia.
  - destruct (N.eqb_spec a 0) as [E|E];
    cbn[N'to_nat]; lia.
Qed.

Lemma N'toN_spec n:
  N.to_nat (N'toN n) = N'to_nat n.
Proof.
  destruct n as [n|n];
  cbn[N'toN];
  cbn[N'to_nat]; lia.
Qed.

Definition N'of_nat(n:nat):=
let x := Z.of_nat n in
if (x <? wB)%Z then N'uint (of_Z x) else N'N (Z.to_N x).

Definition N'of_nat3(x:nat*nat*nat):N'*N'*N' :=
let '(a,b,c):=x in
(N'of_nat a,N'of_nat b,N'of_nat c).

Lemma N'to_of_nat n:
  N'to_nat (N'of_nat n) = n.
Proof.
  unfold N'of_nat,N'to_nat.
  destruct (Z.ltb_spec (Z.of_nat n) wB) as [E|E].
  - rewrite <-is_int.
    1:lia.
    unfold wB in E.
    unfold digits.
    unfold size in E.
    change (to_Z 63) with (Z.of_nat 63).
    lia.
  - lia.
Qed.

Lemma N'to_of_nat3 x:
  N'to_nat3 (N'of_nat3 x) = x.
Proof.
  destruct x as [[a b] c].
  cbn.
  repeat rewrite N'to_of_nat.
  reflexivity.
Qed.



Definition N'parse(x:Z):option N' :=
let y := of_Z x in
if (to_Z y =? x)%Z then Some (N'uint y) else None.

Definition N'print(x:N'):Z :=
match x with
| N'uint x0 => φ x0
| N'N x0 => Z.of_N x0
end.
End N'.

Import N'.
Import NArith.

Declare Scope N'_scope.
Delimit Scope N'_scope with N'.
Number Notation N' N'parse N'print : N'_scope.

Notation "x + y" := (N'add x y) : N'_scope.
Notation "x - y" := (N'sub x y) : N'_scope.
Notation "x / y" := (N'div x y) : N'_scope.
Notation "x 'mod' y" := (N'mod x y): N'_scope.





Ltac simpl_nat_add_mul :=
  repeat rewrite PeanoNat.Nat.mul_succ_r;
  repeat rewrite PeanoNat.Nat.mul_0_r;
  repeat rewrite PeanoNat.Nat.add_assoc;
  repeat rewrite PeanoNat.Nat.add_0_r;
  repeat rewrite PeanoNat.Nat.add_0_l;
  repeat rewrite PeanoNat.Nat.div_1_r.

Ltac solve_replace_divmod :=
repeat (rewrite N'div_inj || rewrite N'mod_inj);
try reflexivity.

Ltac solve_optimize :=
match goal with
| |-
  match ?a0 with
  | _ => _
  end =
match
  match N'OS ?a with
  | _ => _
  end
with _ => _ end
=>
  replace a0 with (N'to_nat a); [
  pose proof (N'OS_spec a) as E;
  destruct (N'OS a) as [?a'|]; repeat rewrite E; pose proof E as ?E0; clear E;
  solve_optimize
  | solve_replace_divmod ]
| |- Some _ = Some _ => f_equal; solve_optimize
| |- (_,_) = (_,_) => f_equal; solve_optimize
| _ => try congruence
end.


