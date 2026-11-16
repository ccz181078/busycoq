From Coq Require Import Uint63 ZArith Lia.

Local Open Scope Z_scope.

Fixpoint tree (A : Type) (n : nat) : Type :=
  match n with
  | O => A
  | S m => (tree A m * tree A m)%type
  end.

Definition Leaf {A : Type} (x : A) : tree A 0 := x.
Definition Node {A : Type} {n : nat} (l r : tree A n) : tree A (S n) := (l, r).

Module Type NTTBaseCfg.
  Parameter modulus : Uint63.int.
  Parameter root : nat -> Uint63.int.
  Parameter inv_root : nat -> Uint63.int.
  Parameter inv_pow2 : nat -> Uint63.int.
  Parameter modulus_range : (1 < Uint63.to_Z modulus < Uint63.wB)%Z.
  Parameter root_range : forall n, (0 <= Uint63.to_Z (root n) < Uint63.to_Z modulus)%Z.
  Parameter inv_root_range : forall n, (0 <= Uint63.to_Z (inv_root n) < Uint63.to_Z modulus)%Z.
  Parameter inv_pow2_range : forall n, (0 <= Uint63.to_Z (inv_pow2 n) < Uint63.to_Z modulus)%Z.
  Parameter two_modulus_le_wB : (2 * Uint63.to_Z modulus <= Uint63.wB)%Z.
  Parameter modulus_square_le_wB :
    (Uint63.to_Z modulus * Uint63.to_Z modulus <= Uint63.wB)%Z.
End NTTBaseCfg.

Module TreeNTT (C : NTTBaseCfg).
  Definition int := Uint63.int.
  Definition modulus : int := C.modulus.
  Definition root : nat -> int := C.root.
  Definition inv_root : nat -> int := C.inv_root.
  Definition inv_pow2 : nat -> int := C.inv_pow2.
  Definition modulus_z : Z := Uint63.to_Z modulus.

  Record block8 := Block8
    { b0 : int;
      b1 : int;
      b2 : int;
      b3 : int;
      b4 : int;
      b5 : int;
      b6 : int;
      b7 : int }.

  Record block16 := Block16
    { c0 : int;
      c1 : int;
      c2 : int;
      c3 : int;
      c4 : int;
      c5 : int;
      c6 : int;
      c7 : int;
      c8 : int;
      c9 : int;
      c10 : int;
      c11 : int;
      c12 : int;
      c13 : int;
      c14 : int;
      c15 : int }.

  Definition pow2 (n : nat) : nat := Nat.pow 2 n.

  Definition value (x : int) : Z := Uint63.to_Z x.
  Definition canonical (x : int) : Prop := (0 <= value x < modulus_z)%Z.

  Definition zcanon (z : Z) : Z := z mod modulus_z.
  Definition zzero : Z := 0.
  Definition zone : Z := 1.
  Definition zadd (x y : Z) : Z := zcanon (x + y).
  Definition zsub (x y : Z) : Z := zcanon (x - y).
  Definition zmul (x y : Z) : Z := zcanon (x * y).

  Fixpoint zpow (x : Z) (n : nat) : Z :=
    match n with
    | O => zone
    | S m => zmul (zpow x m) x
    end.

  Fixpoint zsum (n : nat) (f : nat -> Z) : Z :=
    match n with
    | O => zzero
    | S m => zadd (zsum m f) (f m)
    end.

  Definition repr (z : Z) : int := Uint63.of_Z z.
  Definition zero : int := repr 0.
  Definition one : int := repr 1.

  Definition add_mod (x y : int) : int := repr (zadd (value x) (value y)).
  Definition sub_mod (x y : int) : int := repr (zsub (value x) (value y)).
  Definition mul_mod (x y : int) : int := repr (zmul (value x) (value y)).

  Definition add_mod_fast (x y : int) : int :=
    let s := Uint63.add x y in
    if Uint63.ltb s modulus then s else Uint63.sub s modulus.

  Definition sub_mod_fast (x y : int) : int :=
    if Uint63.ltb x y then Uint63.sub (Uint63.add x modulus) y else Uint63.sub x y.

  Definition mul_mod_fast (x y : int) : int :=
    Uint63.mod (Uint63.mul x y) modulus.

  Fixpoint pow_mod (x : int) (n : nat) : int :=
    match n with
    | O => one
    | S m => mul_mod (pow_mod x m) x
    end.

  Fixpoint map_tree {A B : Type} (n : nat) (f : A -> B) : tree A n -> tree B n :=
    match n with
    | O => f
    | S m =>
        fun t =>
          let '(l, r) := t in
          (map_tree m f l, map_tree m f r)
    end.

  Definition scale_tree (n : nat) (c : int) : tree int n -> tree int n :=
    map_tree n (mul_mod c).

  Definition scale_tree_fast (n : nat) (c : int) : tree int n -> tree int n :=
    map_tree n (mul_mod_fast c).

  Fixpoint zip_tree {A B C0 : Type} (n : nat)
      (f : A -> B -> C0) : tree A n -> tree B n -> tree C0 n :=
    match n with
    | O => f
    | S m =>
        fun x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          (zip_tree m f xl yl, zip_tree m f xr yr)
    end.

  Fixpoint input_get (n : nat) : tree int n -> nat -> int :=
    match n as n0 return tree int n0 -> nat -> int with
    | O => fun t _ => t
    | S m =>
        fun t i =>
          let '(l, r) := t in
          if Nat.even i then input_get m l (Nat.div2 i) else input_get m r (Nat.div2 i)
    end.

  Fixpoint output_get (n : nat) : tree int n -> nat -> int :=
    match n as n0 return tree int n0 -> nat -> int with
    | O => fun t _ => t
    | S m =>
        fun t k =>
          let '(l, r) := t in
          if Nat.ltb k (pow2 m) then
            output_get m l k
          else
            output_get m r (Nat.sub k (pow2 m))
    end.

  Fixpoint canonical_tree (n : nat) : tree int n -> Prop :=
    match n as n0 return tree int n0 -> Prop with
    | O => fun t => canonical t
    | S m =>
        fun t =>
          let '(l, r) := t in
          canonical_tree m l /\ canonical_tree m r
    end.

  Definition pack_block8 (t : tree int 3) : block8 :=
    let '(((x0, x1), (x2, x3)), ((x4, x5), (x6, x7))) := t in
    Block8 x0 x1 x2 x3 x4 x5 x6 x7.

  Definition unpack_block8 (x : block8) : tree int 3 :=
    let '{| b0 := x0; b1 := x1; b2 := x2; b3 := x3;
            b4 := x4; b5 := x5; b6 := x6; b7 := x7 |} := x in
    (((x0, x1), (x2, x3)), ((x4, x5), (x6, x7))).

  Fixpoint pack_tree8 (k : nat) : tree int (S (S (S k))) -> tree block8 k :=
    match k as k0 return tree int (S (S (S k0))) -> tree block8 k0 with
    | O => pack_block8
    | S m =>
        fun t =>
          let '(l, r) := t in
          (pack_tree8 m l, pack_tree8 m r)
    end.

  Fixpoint unpack_tree8 (k : nat) : tree block8 k -> tree int (S (S (S k))) :=
    match k as k0 return tree block8 k0 -> tree int (S (S (S k0))) with
    | O => unpack_block8
    | S m =>
        fun t =>
          let '(l, r) := t in
          (unpack_tree8 m l, unpack_tree8 m r)
    end.

  Definition pack_block16 (t : tree int 4) : block16 :=
    let '((((x0, x1), (x2, x3)), ((x4, x5), (x6, x7))),
         (((x8, x9), (x10, x11)), ((x12, x13), (x14, x15)))) := t in
    Block16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

  Definition unpack_block16 (x : block16) : tree int 4 :=
    let '{| c0 := x0; c1 := x1; c2 := x2; c3 := x3;
            c4 := x4; c5 := x5; c6 := x6; c7 := x7;
            c8 := x8; c9 := x9; c10 := x10; c11 := x11;
            c12 := x12; c13 := x13; c14 := x14; c15 := x15 |} := x in
    ((((x0, x1), (x2, x3)), ((x4, x5), (x6, x7))),
     (((x8, x9), (x10, x11)), ((x12, x13), (x14, x15)))).

  Definition split_block16 (x : block16) : block8 * block8 :=
    let '{| c0 := x0; c1 := x1; c2 := x2; c3 := x3;
            c4 := x4; c5 := x5; c6 := x6; c7 := x7;
            c8 := x8; c9 := x9; c10 := x10; c11 := x11;
            c12 := x12; c13 := x13; c14 := x14; c15 := x15 |} := x in
    (Block8 x0 x1 x2 x3 x4 x5 x6 x7,
     Block8 x8 x9 x10 x11 x12 x13 x14 x15).

  Definition join_block16 (l r : block8) : block16 :=
    let '{| b0 := x0; b1 := x1; b2 := x2; b3 := x3;
            b4 := x4; b5 := x5; b6 := x6; b7 := x7 |} := l in
    let '{| b0 := x8; b1 := x9; b2 := x10; b3 := x11;
            b4 := x12; b5 := x13; b6 := x14; b7 := x15 |} := r in
    Block16 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

  Fixpoint pack_tree16 (k : nat) : tree int (S (S (S (S k)))) -> tree block16 k :=
    match k as k0 return tree int (S (S (S (S k0)))) -> tree block16 k0 with
    | O => pack_block16
    | S m =>
        fun t =>
          let '(l, r) := t in
          (pack_tree16 m l, pack_tree16 m r)
    end.

  Fixpoint unpack_tree16 (k : nat) : tree block16 k -> tree int (S (S (S (S k)))) :=
    match k as k0 return tree block16 k0 -> tree int (S (S (S (S k0)))) with
    | O => unpack_block16
    | S m =>
        fun t =>
          let '(l, r) := t in
          (unpack_tree16 m l, unpack_tree16 m r)
    end.

  Fixpoint twiddle_from (n : nat) : int -> nat -> tree int n -> tree int n :=
    match n as n0 return int -> nat -> tree int n0 -> tree int n0 with
    | O => fun omega base t => mul_mod (pow_mod omega base) t
    | S m =>
        fun omega base t =>
          let '(l, r) := t in
          (twiddle_from m omega base l,
           twiddle_from m omega (Nat.add base (pow2 m)) r)
    end.

  Definition twiddle_tree (n : nat) (omega : int) (t : tree int n) : tree int n :=
    twiddle_from n omega 0 t.

  Fixpoint twiddle_acc (n : nat) : int -> int -> tree int n -> tree int n * int :=
    match n as n0 return int -> int -> tree int n0 -> tree int n0 * int with
    | O =>
        fun omega w t =>
          (mul_mod w t, mul_mod w omega)
    | S m =>
        fun omega w t =>
          let '(l, r) := t in
          let '(l1, w1) := twiddle_acc m omega w l in
          let '(r1, w2) := twiddle_acc m omega w1 r in
          ((l1, r1), w2)
    end.

  Definition twiddle_tree_fast (n : nat) (omega : int) (t : tree int n) : tree int n :=
    fst (twiddle_acc n omega one t).

  Fixpoint butterfly_tree (n : nat) : tree int n -> tree int n -> tree int n * tree int n :=
    match n as n0 return tree int n0 -> tree int n0 -> tree int n0 * tree int n0 with
    | O =>
        fun x y => (add_mod x y, sub_mod x y)
    | S m =>
        fun x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          let '(sl, dl) := butterfly_tree m xl yl in
          let '(sr, dr) := butterfly_tree m xr yr in
          ((sl, sr), (dl, dr))
    end.

  Fixpoint twiddle_acc_u63 (n : nat) : int -> int -> tree int n -> tree int n * int :=
    match n as n0 return int -> int -> tree int n0 -> tree int n0 * int with
    | O =>
        fun omega w t =>
          (mul_mod_fast w t, mul_mod_fast w omega)
    | S m =>
        fun omega w t =>
          let '(l, r) := t in
          let '(l1, w1) := twiddle_acc_u63 m omega w l in
          let '(r1, w2) := twiddle_acc_u63 m omega w1 r in
          ((l1, r1), w2)
    end.

  Definition twiddle_tree_u63 (n : nat) (omega : int) (t : tree int n) : tree int n :=
    fst (twiddle_acc_u63 n omega one t).

  Fixpoint butterfly_tree_u63 (n : nat) : tree int n -> tree int n -> tree int n * tree int n :=
    match n as n0 return tree int n0 -> tree int n0 -> tree int n0 * tree int n0 with
    | O =>
        fun x y => (add_mod_fast x y, sub_mod_fast x y)
    | S m =>
        fun x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          let '(sl, dl) := butterfly_tree_u63 m xl yl in
          let '(sr, dr) := butterfly_tree_u63 m xr yr in
          ((sl, sr), (dl, dr))
    end.

  Fixpoint twiddle_butterfly_acc (n : nat)
      : int -> int -> tree int n -> tree int n -> (tree int n * tree int n) * int :=
    match n as n0 return int -> int -> tree int n0 -> tree int n0 -> (tree int n0 * tree int n0) * int with
    | O =>
        fun omega w x y =>
          let wy := mul_mod_fast w y in
          ((add_mod_fast x wy, sub_mod_fast x wy), mul_mod_fast w omega)
    | S m =>
        fun omega w x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          let '((sl, dl), w1) := twiddle_butterfly_acc m omega w xl yl in
          let '((sr, dr), w2) := twiddle_butterfly_acc m omega w1 xr yr in
          (((sl, sr), (dl, dr)), w2)
    end.

  Definition ntt_fast_1 (t : tree int 1) : tree int 1 :=
    let '(a, b) := t in
    (add_mod_fast a b, sub_mod_fast a b).

  Definition ntt_fast_2 (t : tree int 2) : tree int 2 :=
    let '(l, r) := t in
    let '(l0, l1) := ntt_fast_1 l in
    let '(r0, r1) := ntt_fast_1 r in
    let wr1 := mul_mod_fast (root 2) r1 in
    ((add_mod_fast l0 r0, add_mod_fast l1 wr1),
     (sub_mod_fast l0 r0, sub_mod_fast l1 wr1)).

  Definition ntt_fast_3 (t : tree int 3) : tree int 3 :=
    let '(l, r) := t in
    let '((l0, l1), (l2, l3)) := ntt_fast_2 l in
    let '((r0, r1), (r2, r3)) := ntt_fast_2 r in
    let w := root 3 in
    let w2 := mul_mod_fast w w in
    let w3 := mul_mod_fast w2 w in
    let tr1 := mul_mod_fast w r1 in
    let tr2 := mul_mod_fast w2 r2 in
    let tr3 := mul_mod_fast w3 r3 in
    (((add_mod_fast l0 r0, add_mod_fast l1 tr1),
      (add_mod_fast l2 tr2, add_mod_fast l3 tr3)),
     ((sub_mod_fast l0 r0, sub_mod_fast l1 tr1),
      (sub_mod_fast l2 tr2, sub_mod_fast l3 tr3))).

  Fixpoint ntt_fast_pairs_ge3 (k : nat) : tree int (S (S (S k))) -> tree int (S (S (S k))) :=
    match k as k0 return tree int (S (S (S k0))) -> tree int (S (S (S k0))) with
    | O => ntt_fast_3
    | S m =>
        fun t =>
          let '(l, r) := t in
          let even_part := ntt_fast_pairs_ge3 m l in
          let odd_part := ntt_fast_pairs_ge3 m r in
          fst (twiddle_butterfly_acc (S (S (S m)))
                 (root (S (S (S (S m))))) one even_part odd_part)
    end.

  Definition ntt_fast_pairs (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S O => ntt_fast_1
    | S (S O) => ntt_fast_2
    | S (S (S k)) => ntt_fast_pairs_ge3 k
    end.

  Definition ntt_block8 (x : block8) : block8 :=
    pack_block8 (ntt_fast_3 (unpack_block8 x)).

  Definition twiddle_butterfly_block8 (omega w : int) (x y : block8)
      : (block8 * block8) * int :=
    let '{| b0 := x0; b1 := x1; b2 := x2; b3 := x3;
            b4 := x4; b5 := x5; b6 := x6; b7 := x7 |} := x in
    let '{| b0 := y0; b1 := y1; b2 := y2; b3 := y3;
            b4 := y4; b5 := y5; b6 := y6; b7 := y7 |} := y in
    let wy0 := mul_mod_fast w y0 in
    let w1 := mul_mod_fast w omega in
    let wy1 := mul_mod_fast w1 y1 in
    let w2 := mul_mod_fast w1 omega in
    let wy2 := mul_mod_fast w2 y2 in
    let w3 := mul_mod_fast w2 omega in
    let wy3 := mul_mod_fast w3 y3 in
    let w4 := mul_mod_fast w3 omega in
    let wy4 := mul_mod_fast w4 y4 in
    let w5 := mul_mod_fast w4 omega in
    let wy5 := mul_mod_fast w5 y5 in
    let w6 := mul_mod_fast w5 omega in
    let wy6 := mul_mod_fast w6 y6 in
    let w7 := mul_mod_fast w6 omega in
    let wy7 := mul_mod_fast w7 y7 in
    let w8 := mul_mod_fast w7 omega in
    ((Block8 (add_mod_fast x0 wy0) (add_mod_fast x1 wy1)
             (add_mod_fast x2 wy2) (add_mod_fast x3 wy3)
             (add_mod_fast x4 wy4) (add_mod_fast x5 wy5)
             (add_mod_fast x6 wy6) (add_mod_fast x7 wy7),
      Block8 (sub_mod_fast x0 wy0) (sub_mod_fast x1 wy1)
             (sub_mod_fast x2 wy2) (sub_mod_fast x3 wy3)
             (sub_mod_fast x4 wy4) (sub_mod_fast x5 wy5)
             (sub_mod_fast x6 wy6) (sub_mod_fast x7 wy7)),
     w8).

  Fixpoint twiddle_butterfly_acc_block8 (n : nat)
      : int -> int -> tree block8 n -> tree block8 n -> (tree block8 n * tree block8 n) * int :=
    match n as n0
      return int -> int -> tree block8 n0 -> tree block8 n0 -> (tree block8 n0 * tree block8 n0) * int with
    | O => twiddle_butterfly_block8
    | S m =>
        fun omega w x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          let '((sl, dl), w1) := twiddle_butterfly_acc_block8 m omega w xl yl in
          let '((sr, dr), w2) := twiddle_butterfly_acc_block8 m omega w1 xr yr in
          (((sl, sr), (dl, dr)), w2)
    end.

  Fixpoint ntt_fast_block8_ge3 (k : nat) : tree block8 k -> tree block8 k :=
    match k as k0 return tree block8 k0 -> tree block8 k0 with
    | O => ntt_block8
    | S m =>
        fun t =>
          let '(l, r) := t in
          let even_part := ntt_fast_block8_ge3 m l in
          let odd_part := ntt_fast_block8_ge3 m r in
          fst (twiddle_butterfly_acc_block8 m
                 (root (S (S (S (S m))))) one even_part odd_part)
    end.

  Definition ntt_fast_record8 (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S O => ntt_fast_1
    | S (S O) => ntt_fast_2
    | S (S (S k)) =>
        fun t => unpack_tree8 k (ntt_fast_block8_ge3 k (pack_tree8 k t))
    end.

  Definition ntt_fast_2_with (rootf : nat -> int) (t : tree int 2) : tree int 2 :=
    let '(l, r) := t in
    let '(l0, l1) := ntt_fast_1 l in
    let '(r0, r1) := ntt_fast_1 r in
    let wr1 := mul_mod_fast (rootf 2%nat) r1 in
    ((add_mod_fast l0 r0, add_mod_fast l1 wr1),
     (sub_mod_fast l0 r0, sub_mod_fast l1 wr1)).

  Definition ntt_fast_3_with (rootf : nat -> int) (t : tree int 3) : tree int 3 :=
    let '(l, r) := t in
    let '((l0, l1), (l2, l3)) := ntt_fast_2_with rootf l in
    let '((r0, r1), (r2, r3)) := ntt_fast_2_with rootf r in
    let w := rootf 3%nat in
    let w2 := mul_mod_fast w w in
    let w3 := mul_mod_fast w2 w in
    let tr1 := mul_mod_fast w r1 in
    let tr2 := mul_mod_fast w2 r2 in
    let tr3 := mul_mod_fast w3 r3 in
    (((add_mod_fast l0 r0, add_mod_fast l1 tr1),
      (add_mod_fast l2 tr2, add_mod_fast l3 tr3)),
     ((sub_mod_fast l0 r0, sub_mod_fast l1 tr1),
      (sub_mod_fast l2 tr2, sub_mod_fast l3 tr3))).

  Definition ntt_block8_with (rootf : nat -> int) (x : block8) : block8 :=
    pack_block8 (ntt_fast_3_with rootf (unpack_block8 x)).

  Fixpoint ntt_fast_pairs_ge3_with (rootf : nat -> int) (k : nat)
      : tree int (S (S (S k))) -> tree int (S (S (S k))) :=
    match k as k0 return tree int (S (S (S k0))) -> tree int (S (S (S k0))) with
    | O => ntt_fast_3_with rootf
    | S m =>
        fun t =>
          let '(l, r) := t in
          let even_part := ntt_fast_pairs_ge3_with rootf m l in
          let odd_part := ntt_fast_pairs_ge3_with rootf m r in
          fst (twiddle_butterfly_acc (S (S (S m)))
                 (rootf (S (S (S (S m))))) one even_part odd_part)
    end.

  Definition ntt_fast_pairs_with (rootf : nat -> int) (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S O => ntt_fast_1
    | S (S O) => ntt_fast_2_with rootf
    | S (S (S k)) => ntt_fast_pairs_ge3_with rootf k
    end.

  Fixpoint ntt_fast_block8_ge3_with (rootf : nat -> int) (k : nat)
      : tree block8 k -> tree block8 k :=
    match k as k0 return tree block8 k0 -> tree block8 k0 with
    | O => ntt_block8_with rootf
    | S m =>
        fun t =>
          let '(l, r) := t in
          let even_part := ntt_fast_block8_ge3_with rootf m l in
          let odd_part := ntt_fast_block8_ge3_with rootf m r in
          fst (twiddle_butterfly_acc_block8 m
                 (rootf (S (S (S (S m))))) one even_part odd_part)
    end.

  Definition ntt_fast_record8_with (rootf : nat -> int) (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S O => ntt_fast_1
    | S (S O) => ntt_fast_2_with rootf
    | S (S (S k)) =>
        fun t => unpack_tree8 k (ntt_fast_block8_ge3_with rootf k (pack_tree8 k t))
    end.

  Fixpoint intt_fast_tree_raw (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S m =>
        fun t =>
          let '(l, r) := t in
          let '(summed, diffed) := butterfly_tree_u63 m l r in
          let twiddled := twiddle_tree_u63 m (inv_root (S m)) diffed in
          (intt_fast_tree_raw m summed, intt_fast_tree_raw m twiddled)
    end.

  Fixpoint butterfly_twiddle_acc_tree (n : nat)
      : int -> int -> tree int n -> tree int n -> (tree int n * tree int n) * int :=
    match n as n0
      return int -> int -> tree int n0 -> tree int n0 -> (tree int n0 * tree int n0) * int with
    | O =>
        fun omega w x y =>
          let s := add_mod_fast x y in
          let d := mul_mod_fast w (sub_mod_fast x y) in
          ((s, d), mul_mod_fast w omega)
    | S m =>
        fun omega w x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          let '((sl, dl), w1) := butterfly_twiddle_acc_tree m omega w xl yl in
          let '((sr, dr), w2) := butterfly_twiddle_acc_tree m omega w1 xr yr in
          (((sl, sr), (dl, dr)), w2)
    end.

  Definition intt_block8_raw (x : block8) : block8 :=
    pack_block8 (intt_fast_tree_raw 3%nat (unpack_block8 x)).

  Definition butterfly_twiddle_block8 (omega w : int) (x y : block8)
      : (block8 * block8) * int :=
    let '{| b0 := x0; b1 := x1; b2 := x2; b3 := x3;
            b4 := x4; b5 := x5; b6 := x6; b7 := x7 |} := x in
    let '{| b0 := y0; b1 := y1; b2 := y2; b3 := y3;
            b4 := y4; b5 := y5; b6 := y6; b7 := y7 |} := y in
    let s0 := add_mod_fast x0 y0 in
    let d0 := mul_mod_fast w (sub_mod_fast x0 y0) in
    let w1 := mul_mod_fast w omega in
    let s1 := add_mod_fast x1 y1 in
    let d1 := mul_mod_fast w1 (sub_mod_fast x1 y1) in
    let w2 := mul_mod_fast w1 omega in
    let s2 := add_mod_fast x2 y2 in
    let d2 := mul_mod_fast w2 (sub_mod_fast x2 y2) in
    let w3 := mul_mod_fast w2 omega in
    let s3 := add_mod_fast x3 y3 in
    let d3 := mul_mod_fast w3 (sub_mod_fast x3 y3) in
    let w4 := mul_mod_fast w3 omega in
    let s4 := add_mod_fast x4 y4 in
    let d4 := mul_mod_fast w4 (sub_mod_fast x4 y4) in
    let w5 := mul_mod_fast w4 omega in
    let s5 := add_mod_fast x5 y5 in
    let d5 := mul_mod_fast w5 (sub_mod_fast x5 y5) in
    let w6 := mul_mod_fast w5 omega in
    let s6 := add_mod_fast x6 y6 in
    let d6 := mul_mod_fast w6 (sub_mod_fast x6 y6) in
    let w7 := mul_mod_fast w6 omega in
    let s7 := add_mod_fast x7 y7 in
    let d7 := mul_mod_fast w7 (sub_mod_fast x7 y7) in
    let w8 := mul_mod_fast w7 omega in
    ((Block8 s0 s1 s2 s3 s4 s5 s6 s7,
      Block8 d0 d1 d2 d3 d4 d5 d6 d7),
     w8).

  Fixpoint butterfly_twiddle_acc_block8 (n : nat)
      : int -> int -> tree block8 n -> tree block8 n -> (tree block8 n * tree block8 n) * int :=
    match n as n0
      return int -> int -> tree block8 n0 -> tree block8 n0 -> (tree block8 n0 * tree block8 n0) * int with
    | O => butterfly_twiddle_block8
    | S m =>
        fun omega w x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          let '((sl, dl), w1) := butterfly_twiddle_acc_block8 m omega w xl yl in
          let '((sr, dr), w2) := butterfly_twiddle_acc_block8 m omega w1 xr yr in
          (((sl, sr), (dl, dr)), w2)
    end.

  Fixpoint intt_fast_block8_ge3_raw (k : nat) : tree block8 k -> tree block8 k :=
    match k as k0 return tree block8 k0 -> tree block8 k0 with
    | O => intt_block8_raw
    | S m =>
        fun t =>
          let '(l, r) := t in
          let '((summed, diffed), _) := butterfly_twiddle_acc_block8 m
              (inv_root (S (S (S (S m))))) one l r in
          (intt_fast_block8_ge3_raw m summed, intt_fast_block8_ge3_raw m diffed)
    end.

  Definition intt_fast_record8_raw (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S O => intt_fast_tree_raw 1%nat
    | S (S O) => intt_fast_tree_raw 2%nat
    | S (S (S k)) =>
        fun t => unpack_tree8 k (intt_fast_block8_ge3_raw k (pack_tree8 k t))
    end.

  Definition intt_fast_record8 (n : nat) : tree int n -> tree int n :=
    fun t => scale_tree_fast n (inv_pow2 n) (intt_fast_record8_raw n t).

  Definition intt_fast : forall n, tree int n -> tree int n := intt_fast_record8.

  Definition ntt_block16 (x : block16) : block16 :=
    let '(l, r) := split_block16 x in
    let l1 := ntt_block8 l in
    let r1 := ntt_block8 r in
    let '((sl, dl), _) := twiddle_butterfly_block8 (root 4) one l1 r1 in
    join_block16 sl dl.

  Definition twiddle_butterfly_block16 (omega w : int) (x y : block16)
      : (block16 * block16) * int :=
    let '(xl, xr) := split_block16 x in
    let '(yl, yr) := split_block16 y in
    let '((sl, dl), w1) := twiddle_butterfly_block8 omega w xl yl in
    let '((sr, dr), w2) := twiddle_butterfly_block8 omega w1 xr yr in
    ((join_block16 sl sr, join_block16 dl dr), w2).

  Fixpoint twiddle_butterfly_acc_block16 (n : nat)
      : int -> int -> tree block16 n -> tree block16 n -> (tree block16 n * tree block16 n) * int :=
    match n as n0
      return int -> int -> tree block16 n0 -> tree block16 n0 -> (tree block16 n0 * tree block16 n0) * int with
    | O => twiddle_butterfly_block16
    | S m =>
        fun omega w x y =>
          let '(xl, xr) := x in
          let '(yl, yr) := y in
          let '((sl, dl), w1) := twiddle_butterfly_acc_block16 m omega w xl yl in
          let '((sr, dr), w2) := twiddle_butterfly_acc_block16 m omega w1 xr yr in
          (((sl, sr), (dl, dr)), w2)
    end.

  Fixpoint ntt_fast_block16_ge4 (k : nat) : tree block16 k -> tree block16 k :=
    match k as k0 return tree block16 k0 -> tree block16 k0 with
    | O => ntt_block16
    | S m =>
        fun t =>
          let '(l, r) := t in
          let even_part := ntt_fast_block16_ge4 m l in
          let odd_part := ntt_fast_block16_ge4 m r in
          fst (twiddle_butterfly_acc_block16 m
                 (root (S (S (S (S (S m)))))) one even_part odd_part)
    end.

  Definition ntt_fast_record16 (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S O => ntt_fast_1
    | S (S O) => ntt_fast_2
    | S (S (S O)) => ntt_fast_3
    | S (S (S (S k))) =>
        fun t => unpack_tree16 k (ntt_fast_block16_ge4 k (pack_tree16 k t))
    end.

  Definition ntt_fast : forall n, tree int n -> tree int n := ntt_fast_record8.

  Fixpoint ntt_with (rootf : nat -> int) (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S m =>
        fun t =>
          let '(l, r) := t in
          let even_part := ntt_with rootf m l in
          let odd_part := ntt_with rootf m r in
          let twiddled := twiddle_tree m (rootf (S m)) odd_part in
          (zip_tree m add_mod even_part twiddled,
           zip_tree m sub_mod even_part twiddled)
    end.

  Fixpoint intt_raw (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S m =>
        fun t =>
          let '(l, r) := t in
          let summed := zip_tree m add_mod l r in
          let diffed := zip_tree m sub_mod l r in
          let twiddled := twiddle_tree m (inv_root (S m)) diffed in
          (intt_raw m summed, intt_raw m twiddled)
    end.

  Definition intt (n : nat) : tree int n -> tree int n :=
    fun t => scale_tree n (inv_pow2 n) (intt_raw n t).

  Fixpoint ntt (n : nat) : tree int n -> tree int n :=
    match n as n0 return tree int n0 -> tree int n0 with
    | O => fun t => t
    | S m =>
        fun t =>
          let '(l, r) := t in
          let even_part := ntt m l in
          let odd_part := ntt m r in
          let twiddled := twiddle_tree m (root (S m)) odd_part in
          (zip_tree m add_mod even_part twiddled,
           zip_tree m sub_mod even_part twiddled)
    end.

  Fixpoint dft_with (rootf : nat -> int) (n : nat) : tree int n -> nat -> Z :=
    match n as n0 return tree int n0 -> nat -> Z with
    | O => fun t _ => value t
    | S m =>
        fun t k =>
          let '(l, r) := t in
          let even_part := dft_with rootf m l in
          let odd_part := dft_with rootf m r in
          let omega := value (rootf (S m)) in
          if Nat.ltb k (pow2 m) then
            zadd (even_part k) (zmul (zpow omega k) (odd_part k))
          else
            let u := Nat.sub k (pow2 m) in
            zsub (even_part u) (zmul (zpow omega u) (odd_part u))
    end.

  Fixpoint dft (n : nat) : tree int n -> nat -> Z :=
    match n as n0 return tree int n0 -> nat -> Z with
    | O => fun t _ => value t
    | S m =>
        fun t k =>
          let '(l, r) := t in
          let even_part := dft m l in
          let odd_part := dft m r in
          let omega := value (root (S m)) in
          if Nat.ltb k (pow2 m) then
            zadd (even_part k) (zmul (zpow omega k) (odd_part k))
          else
            let u := Nat.sub k (pow2 m) in
            zsub (even_part u) (zmul (zpow omega u) (odd_part u))
    end.

  Definition idft_raw (n : nat) : tree int n -> nat -> Z :=
    dft_with inv_root n.

  Definition idft (n : nat) (t : tree int n) (k : nat) : Z :=
    zmul (value (inv_pow2 n)) (idft_raw n t k).

  Fixpoint idft_dif_raw (n : nat) : tree int n -> nat -> Z :=
    match n as n0 return tree int n0 -> nat -> Z with
    | O => fun t _ => value t
    | S m =>
        fun t i =>
          let '(l, r) := t in
          if Nat.even i then
            idft_dif_raw m (zip_tree m add_mod l r) (Nat.div2 i)
          else
            idft_dif_raw m (twiddle_tree m (inv_root (S m)) (zip_tree m sub_mod l r)) (Nat.div2 i)
    end.

  Definition idft_dif (n : nat) (t : tree int n) (i : nat) : Z :=
    zmul (value (inv_pow2 n)) (idft_dif_raw n t i).

  Lemma modulus_pos : (0 < modulus_z)%Z.
  Proof.
    destruct C.modulus_range as [Hgt _].
    eapply Z.lt_trans.
    - exact Z.lt_0_1.
    - exact Hgt.
  Qed.

  Lemma modulus_lt_wB : (modulus_z < Uint63.wB)%Z.
  Proof.
    destruct C.modulus_range as [_ Hlt].
    exact Hlt.
  Qed.

  Lemma modulus_nonzero : modulus_z <> 0%Z.
  Proof.
    intro H0.
    pose proof modulus_pos as Hpos.
    rewrite H0 in Hpos.
    exact (Z.lt_irrefl 0 Hpos).
  Qed.

  Lemma zcanon_range : forall z, (0 <= zcanon z < modulus_z)%Z.
  Proof.
    intros z.
    unfold zcanon.
    apply Z.mod_pos_bound.
    exact modulus_pos.
  Qed.

  Lemma zcanon_small : forall z, (0 <= z < modulus_z)%Z -> zcanon z = z.
  Proof.
    intros z Hz.
    unfold zcanon.
    apply Z.mod_small.
    exact Hz.
  Qed.

  Lemma zcanon_idem : forall z, zcanon (zcanon z) = zcanon z.
  Proof.
    intros z.
    unfold zcanon.
    rewrite Z.mod_mod by exact modulus_nonzero.
    reflexivity.
  Qed.

  Lemma zcanon_large : forall z,
      (modulus_z <= z < 2 * modulus_z)%Z ->
      zcanon z = (z - modulus_z)%Z.
  Proof.
    intros z Hz.
    unfold zcanon.
    apply eq_sym.
    apply Z.mod_unique with (q := 1).
    - left. split; lia.
    - lia.
  Qed.

  Lemma zcanon_neg : forall z,
      (- modulus_z <= z < 0)%Z ->
      zcanon z = (z + modulus_z)%Z.
  Proof.
    intros z Hz.
    unfold zcanon.
    apply eq_sym.
    apply Z.mod_unique with (q := (-1)%Z).
    - left. split; lia.
    - lia.
  Qed.

  Lemma zcanon_add : forall x y, zcanon (zcanon x + zcanon y) = zcanon (x + y).
  Proof.
    intros x y.
    unfold zcanon.
    rewrite Zplus_mod_idemp_l.
    rewrite Zplus_mod_idemp_r.
    reflexivity.
  Qed.

  Lemma zcanon_add_idemp_l : forall x y, zcanon (zcanon x + y) = zcanon (x + y).
  Proof.
    intros x y.
    unfold zcanon.
    rewrite Zplus_mod_idemp_l.
    reflexivity.
  Qed.

  Lemma zcanon_add_idemp_r : forall x y, zcanon (x + zcanon y) = zcanon (x + y).
  Proof.
    intros x y.
    unfold zcanon.
    rewrite Zplus_mod_idemp_r.
    reflexivity.
  Qed.

  Lemma zcanon_sub : forall x y, zcanon (zcanon x - zcanon y) = zcanon (x - y).
  Proof.
    intros x y.
    unfold zcanon.
    rewrite Zminus_mod_idemp_l.
    rewrite Zminus_mod_idemp_r.
    reflexivity.
  Qed.

  Lemma zcanon_mul : forall x y, zcanon (zcanon x * zcanon y) = zcanon (x * y).
  Proof.
    intros x y.
    unfold zcanon.
    rewrite Zmult_mod_idemp_l.
    rewrite Zmult_mod_idemp_r.
    reflexivity.
  Qed.

  Lemma zcanon_mul_idemp_l : forall x y, zcanon (zcanon x * y) = zcanon (x * y).
  Proof.
    intros x y.
    unfold zcanon.
    rewrite Zmult_mod_idemp_l.
    reflexivity.
  Qed.

  Lemma zcanon_mul_idemp_r : forall x y, zcanon (x * zcanon y) = zcanon (x * y).
  Proof.
    intros x y.
    unfold zcanon.
    rewrite Zmult_mod_idemp_r.
    reflexivity.
  Qed.

  Lemma zadd_assoc : forall x y z, zadd x (zadd y z) = zadd (zadd x y) z.
  Proof.
    intros x y z.
    unfold zadd.
    rewrite zcanon_add_idemp_r.
    rewrite zcanon_add_idemp_l.
    now rewrite Z.add_assoc.
  Qed.

  Lemma zadd_comm : forall x y, zadd x y = zadd y x.
  Proof.
    intros x y.
    unfold zadd.
    now rewrite Z.add_comm.
  Qed.

  Lemma zadd_0_l : forall x, zadd zzero x = zcanon x.
  Proof.
    intros x.
    unfold zadd, zzero.
    rewrite Z.add_0_l.
    reflexivity.
  Qed.

  Lemma zmul_assoc : forall x y z, zmul x (zmul y z) = zmul (zmul x y) z.
  Proof.
    intros x y z.
    unfold zmul.
    rewrite zcanon_mul_idemp_r.
    rewrite zcanon_mul_idemp_l.
    now rewrite Z.mul_assoc.
  Qed.

  Lemma zmul_comm : forall x y, zmul x y = zmul y x.
  Proof.
    intros x y.
    unfold zmul.
    now rewrite Z.mul_comm.
  Qed.

  Lemma zmul_1_l : forall x, zmul zone x = zcanon x.
  Proof.
    intros x.
    unfold zmul, zone.
    rewrite Z.mul_1_l.
    reflexivity.
  Qed.

  Lemma zmul_add_distr_r : forall x y z,
      zmul (zadd x y) z = zadd (zmul x z) (zmul y z).
  Proof.
    intros x y z.
    unfold zadd, zmul.
    rewrite zcanon_mul_idemp_l.
    rewrite zcanon_add.
    rewrite Z.mul_add_distr_r.
    reflexivity.
  Qed.

  Lemma value_repr_canon : forall z, value (repr (zcanon z)) = zcanon z.
  Proof.
    intros z.
    unfold value, repr.
    rewrite Uint63.of_Z_spec.
    apply Z.mod_small.
    destruct (zcanon_range z) as [Hz0 Hzlt].
    split.
    - exact Hz0.
    - eapply Z.lt_trans.
      + exact Hzlt.
      + exact modulus_lt_wB.
  Qed.

  Lemma canonical_zero : canonical zero.
  Proof.
    unfold canonical, zero, repr, value.
    rewrite Uint63.of_Z_spec.
    rewrite Z.mod_small.
    2:{
      split.
      - exact (Z.le_refl 0).
      - exact Uint63.wB_pos.
    }
    split.
    - exact (Z.le_refl 0).
    - exact modulus_pos.
  Qed.

  Lemma one_lt_modulus : (1 < modulus_z)%Z.
  Proof.
    destruct C.modulus_range as [Hgt _].
    exact Hgt.
  Qed.

  Lemma zero_le_one : (0 <= 1)%Z.
  Proof.
    lia.
  Qed.

  Lemma one_lt_wB : (1 < Uint63.wB)%Z.
  Proof.
    eapply Z.lt_trans.
    - exact one_lt_modulus.
    - exact modulus_lt_wB.
  Qed.

  Lemma canonical_one : canonical one.
  Proof.
    unfold canonical, one, repr, value.
    rewrite Uint63.of_Z_spec.
    rewrite Z.mod_small.
    2:{
      split.
      - exact zero_le_one.
      - exact one_lt_wB.
    }
    split.
    - exact zero_le_one.
    - exact one_lt_modulus.
  Qed.

  Lemma value_add_mod : forall x y, value (add_mod x y) = zadd (value x) (value y).
  Proof.
    intros x y.
    unfold add_mod, zadd.
    apply value_repr_canon.
  Qed.

  Lemma value_sub_mod : forall x y, value (sub_mod x y) = zsub (value x) (value y).
  Proof.
    intros x y.
    unfold sub_mod, zsub.
    apply value_repr_canon.
  Qed.

  Lemma value_mul_mod : forall x y, value (mul_mod x y) = zmul (value x) (value y).
  Proof.
    intros x y.
    unfold mul_mod, zmul.
    apply value_repr_canon.
  Qed.

  Lemma canonical_root : forall n, canonical (root n).
  Proof.
    intro n.
    unfold canonical, value, modulus_z.
    apply C.root_range.
  Qed.

  Lemma canonical_inv_root : forall n, canonical (inv_root n).
  Proof.
    intro n.
    unfold canonical, value, modulus_z.
    apply C.inv_root_range.
  Qed.

  Lemma canonical_inv_pow2 : forall n, canonical (inv_pow2 n).
  Proof.
    intro n.
    unfold canonical, value, modulus_z.
    apply C.inv_pow2_range.
  Qed.

  Lemma add_mod_fast_eq :
    forall x y,
      canonical x ->
      canonical y ->
      add_mod_fast x y = add_mod x y.
  Proof.
    intros x y Hx Hy.
    apply Uint63.to_Z_inj.
    destruct Hx as [Hx0 Hxlt], Hy as [Hy0 Hylt].
    unfold add_mod_fast, add_mod, repr, zadd, value.
    set (s := Uint63.add x y).
    assert (Hs : Uint63.to_Z s = (Uint63.to_Z x + Uint63.to_Z y)%Z).
    {
      subst s.
      rewrite Uint63.add_spec.
      apply Z.mod_small.
      split.
      - apply Z.add_nonneg_nonneg; assumption.
      - assert (Hsumlt2 : (Uint63.to_Z x + Uint63.to_Z y < modulus_z + modulus_z)%Z).
        {
          apply Z.add_lt_mono; assumption.
        }
        eapply Z.lt_le_trans.
        + exact Hsumlt2.
        + replace (modulus_z + modulus_z)%Z with (2 * modulus_z)%Z by lia.
          exact C.two_modulus_le_wB.
    }
    destruct (Uint63.ltb s modulus) eqn:Hcmp.
    - apply Uint63.ltb_spec in Hcmp.
      rewrite Hs.
      rewrite value_repr_canon.
      symmetry.
      apply Z.mod_small.
      split.
      + apply Z.add_nonneg_nonneg; assumption.
      + rewrite <- Hs.
        exact Hcmp.
    - rewrite Uint63.sub_spec.
      rewrite Hs.
      assert (Hnlt : ~ (Uint63.to_Z x + Uint63.to_Z y < modulus_z)%Z).
      {
        intro Hlt.
        assert (Hslt : (Uint63.to_Z s < modulus_z)%Z).
        {
          rewrite Hs.
          exact Hlt.
        }
        pose proof (proj2 (Uint63.ltb_spec s modulus) Hslt) as Htrue.
        rewrite Hcmp in Htrue.
        discriminate.
      }
      assert (Hsum_ge : (modulus_z <= Uint63.to_Z x + Uint63.to_Z y)%Z) by lia.
      assert (Hsum_lt' : (Uint63.to_Z x + Uint63.to_Z y < modulus_z + modulus_z)%Z).
      {
        apply Z.add_lt_mono; assumption.
      }
      assert (Hsum_lt : (Uint63.to_Z x + Uint63.to_Z y < 2 * modulus_z)%Z).
      {
        replace (2 * modulus_z)%Z with (modulus_z + modulus_z)%Z by lia.
        exact Hsum_lt'.
      }
      assert (Hdiff : (0 <= Uint63.to_Z x + Uint63.to_Z y - modulus_z < Uint63.wB)%Z).
      {
        split.
        - lia.
        - assert (Hdiff_lt_mod : (Uint63.to_Z x + Uint63.to_Z y - modulus_z < modulus_z)%Z) by lia.
          eapply Z.lt_trans.
          + exact Hdiff_lt_mod.
          + exact modulus_lt_wB.
      }
      rewrite Z.mod_small by exact Hdiff.
      rewrite value_repr_canon.
      rewrite zcanon_large by lia.
      reflexivity.
  Qed.

  Lemma sub_mod_fast_eq :
    forall x y,
      canonical x ->
      canonical y ->
      sub_mod_fast x y = sub_mod x y.
  Proof.
    intros x y Hx Hy.
    apply Uint63.to_Z_inj.
    destruct Hx as [Hx0 Hxlt], Hy as [Hy0 Hylt].
    unfold sub_mod_fast, sub_mod, repr, zsub, value.
    destruct (Uint63.ltb x y) eqn:Hcmp.
    - apply Uint63.ltb_spec in Hcmp.
      rewrite Uint63.sub_spec.
      rewrite Uint63.add_spec.
      assert (Hsum_small : (0 <= Uint63.to_Z x + modulus_z < Uint63.wB)%Z).
      {
        split.
        - apply Z.add_nonneg_nonneg.
          + exact Hx0.
          + apply Z.lt_le_incl.
            exact modulus_pos.
        - eapply Z.lt_le_trans.
          + apply Z.add_lt_mono_r.
            exact Hxlt.
          + replace (modulus_z + modulus_z)%Z with (2 * modulus_z)%Z by lia.
            exact C.two_modulus_le_wB.
      }
      change modulus_z with (Uint63.to_Z modulus) in Hsum_small.
      change modulus_z with (Uint63.to_Z modulus).
      rewrite (Z.mod_small (Uint63.to_Z x + Uint63.to_Z modulus) Uint63.wB Hsum_small).
      assert (Hdiff_small : (0 <= Uint63.to_Z x + modulus_z - Uint63.to_Z y < Uint63.wB)%Z).
      {
        split.
        - replace (Uint63.to_Z x + modulus_z - Uint63.to_Z y)%Z
            with (Uint63.to_Z x + (modulus_z - Uint63.to_Z y))%Z by lia.
          apply Z.add_nonneg_nonneg.
          + exact Hx0.
          + apply Z.sub_nonneg.
            apply Z.lt_le_incl.
            exact Hylt.
        - eapply Z.lt_trans.
          + assert (Htmp : (Uint63.to_Z x + modulus_z - Uint63.to_Z y < modulus_z)%Z).
            {
              assert (Hxyneg : (Uint63.to_Z x - Uint63.to_Z y < 0)%Z) by lia.
              replace (Uint63.to_Z x + modulus_z - Uint63.to_Z y)%Z
                with (modulus_z + (Uint63.to_Z x - Uint63.to_Z y))%Z by lia.
              assert (Htmp2 : (modulus_z + (Uint63.to_Z x - Uint63.to_Z y) < modulus_z)%Z) by lia.
              exact Htmp2.
            }
            exact Htmp.
          + exact modulus_lt_wB.
      }
      rewrite Z.mod_small by exact Hdiff_small.
      rewrite value_repr_canon.
      rewrite zcanon_neg by lia.
      change modulus_z with (Uint63.to_Z modulus).
      replace (Uint63.to_Z x + Uint63.to_Z modulus - Uint63.to_Z y)%Z
        with (Uint63.to_Z x - Uint63.to_Z y + Uint63.to_Z modulus)%Z by lia.
      reflexivity.
    - assert (Hnlt : ~ (Uint63.to_Z x < Uint63.to_Z y)%Z).
      {
        intro Hlt.
        pose proof (proj2 (Uint63.ltb_spec x y) Hlt) as Htrue.
        rewrite Hcmp in Htrue.
        discriminate.
      }
      rewrite Uint63.sub_spec.
      assert (Hdiff_small : (0 <= Uint63.to_Z x - Uint63.to_Z y < Uint63.wB)%Z).
      {
        split.
        - apply Z.sub_nonneg.
          lia.
        - eapply Z.lt_trans.
          + assert (Htmp : (Uint63.to_Z x - Uint63.to_Z y < modulus_z)%Z).
            {
              eapply Z.le_lt_trans.
              - apply (proj1 (Z.le_sub_nonneg (Uint63.to_Z x) (Uint63.to_Z y))).
                exact Hy0.
              - exact Hxlt.
            }
            exact Htmp.
          + exact modulus_lt_wB.
      }
      rewrite Z.mod_small by exact Hdiff_small.
      rewrite value_repr_canon.
      symmetry.
      apply Z.mod_small.
      split.
      + apply Z.sub_nonneg.
        lia.
      + assert (Htmp : (Uint63.to_Z x - Uint63.to_Z y < modulus_z)%Z).
        {
          eapply Z.le_lt_trans.
          + apply (proj1 (Z.le_sub_nonneg (Uint63.to_Z x) (Uint63.to_Z y))).
            exact Hy0.
          + exact Hxlt.
        }
        exact Htmp.
  Qed.

  Lemma mul_mod_fast_eq :
    forall x y,
      canonical x ->
      canonical y ->
      mul_mod_fast x y = mul_mod x y.
  Proof.
    intros x y Hx Hy.
    apply Uint63.to_Z_inj.
    destruct Hx as [Hx0 Hxlt], Hy as [Hy0 Hylt].
    unfold mul_mod_fast, mul_mod, repr, zmul, value.
    rewrite Uint63.mod_spec.
    rewrite Uint63.mul_spec.
    assert (Hprod_small : (0 <= Uint63.to_Z x * Uint63.to_Z y < Uint63.wB)%Z).
    {
      split.
      - apply Z.mul_nonneg_nonneg; assumption.
      - eapply Z.lt_le_trans.
        + assert (Hprod_lt : (Uint63.to_Z x * Uint63.to_Z y < modulus_z * modulus_z)%Z).
          {
            apply Z.mul_lt_mono_nonneg.
            - exact Hx0.
            - exact Hxlt.
            - exact Hy0.
            - exact Hylt.
          }
          exact Hprod_lt.
        + exact C.modulus_square_le_wB.
    }
    replace ((Uint63.to_Z x * Uint63.to_Z y) mod Uint63.wB)%Z
      with (Uint63.to_Z x * Uint63.to_Z y)%Z.
    2:{
      symmetry.
      apply Z.mod_small.
      exact Hprod_small.
    }
    rewrite value_repr_canon.
    reflexivity.
  Qed.

  Lemma canonical_add_mod_fast : forall x y, canonical x -> canonical y -> canonical (add_mod_fast x y).
  Proof.
    intros x y Hx Hy.
    rewrite add_mod_fast_eq by assumption.
    unfold canonical.
    rewrite value_add_mod.
    apply zcanon_range.
  Qed.

  Lemma canonical_sub_mod_fast : forall x y, canonical x -> canonical y -> canonical (sub_mod_fast x y).
  Proof.
    intros x y Hx Hy.
    rewrite sub_mod_fast_eq by assumption.
    unfold canonical.
    rewrite value_sub_mod.
    apply zcanon_range.
  Qed.

  Lemma canonical_mul_mod_fast : forall x y, canonical x -> canonical y -> canonical (mul_mod_fast x y).
  Proof.
    intros x y Hx Hy.
    rewrite mul_mod_fast_eq by assumption.
    unfold canonical.
    rewrite value_mul_mod.
    apply zcanon_range.
  Qed.

  Lemma canonical_add_mod : forall x y, canonical (add_mod x y).
  Proof.
    intros x y.
    unfold canonical.
    rewrite value_add_mod.
    apply zcanon_range.
  Qed.

  Lemma canonical_sub_mod : forall x y, canonical (sub_mod x y).
  Proof.
    intros x y.
    unfold canonical.
    rewrite value_sub_mod.
    apply zcanon_range.
  Qed.

  Lemma canonical_mul_mod : forall x y, canonical (mul_mod x y).
  Proof.
    intros x y.
    unfold canonical.
    rewrite value_mul_mod.
    apply zcanon_range.
  Qed.

  Lemma value_zero : value zero = zzero.
  Proof.
    unfold zzero, zero, repr, value.
    rewrite Uint63.of_Z_spec.
    rewrite Z.mod_small.
    - reflexivity.
    - split.
      + exact (Z.le_refl 0).
      + exact Uint63.wB_pos.
  Qed.

  Lemma value_one : value one = zone.
  Proof.
    unfold zone, one, repr, value.
    rewrite Uint63.of_Z_spec.
    rewrite Z.mod_small.
    - reflexivity.
    - split.
      + exact zero_le_one.
      + exact one_lt_wB.
  Qed.

  Lemma pow2_succ : forall n, pow2 (S n) = (pow2 n + pow2 n)%nat.
  Proof.
    intros n.
    unfold pow2.
    simpl.
    lia.
  Qed.

  Lemma pow2_pos : forall n, (0 < pow2 n)%nat.
  Proof.
    intros n.
    unfold pow2.
    pose proof (Nat.pow_nonzero 2 n) as Hnz.
    assert (H2 : (2 <> 0)%nat) by lia.
    specialize (Hnz H2).
    lia.
  Qed.

  Lemma value_pow_mod : forall x n, value (pow_mod x n) = zpow (value x) n.
  Proof.
    intros x n.
    induction n as [|n IH].
    - simpl.
      exact value_one.
    - simpl.
      rewrite value_mul_mod, IH.
      reflexivity.
  Qed.

  Lemma zpow_range : forall x n, (0 <= zpow x n < modulus_z)%Z.
  Proof.
    intros x n.
    induction n as [|n IH].
    - simpl.
      split.
      + exact zero_le_one.
      + exact one_lt_modulus.
    - simpl.
      apply zcanon_range.
  Qed.

  Lemma canonical_pow_mod : forall x n, canonical (pow_mod x n).
  Proof.
    intros x n.
    unfold canonical.
    rewrite value_pow_mod.
    apply zpow_range.
  Qed.

  Lemma mul_mod_one_r :
    forall x,
      canonical x ->
      mul_mod one x = x.
  Proof.
    intros x Hx.
    apply Uint63.to_Z_inj.
    destruct Hx as [Hx0 Hxlt].
    rewrite value_mul_mod.
    rewrite value_one.
    unfold zmul, zone.
    rewrite Z.mul_1_l.
    apply zcanon_small.
    split; assumption.
  Qed.

  Lemma mul_mod_fast_one_r :
    forall x,
      canonical x ->
      mul_mod_fast one x = x.
  Proof.
    intros x Hx.
    rewrite mul_mod_fast_eq.
    - apply mul_mod_one_r.
      exact Hx.
    - apply canonical_one.
    - exact Hx.
  Qed.

  Lemma scale_tree_fast_eq :
    forall n c (t : tree int n),
      canonical c ->
      canonical_tree n t ->
      scale_tree_fast n c t = scale_tree n c t.
  Proof.
    induction n as [|n IH]; intros c t Hc Ht.
    - simpl.
      apply mul_mod_fast_eq; assumption.
    - destruct t as [l r].
      cbn in *.
      destruct Ht as [Hl Hr].
      change ((scale_tree_fast n c l, scale_tree_fast n c r) =
              (scale_tree n c l, scale_tree n c r)).
      now rewrite (IH c l Hc Hl), (IH c r Hc Hr).
  Qed.

  Lemma canonical_scale_tree :
    forall n c (t : tree int n),
      canonical c ->
      canonical_tree n t ->
      canonical_tree n (scale_tree n c t).
  Proof.
    induction n as [|n IH]; intros c t Hc Ht.
    - simpl.
      apply canonical_mul_mod.
    - destruct t as [l r].
      simpl in *.
      destruct Ht as [Hl Hr].
      split.
      + apply IH; assumption.
      + apply IH; assumption.
  Qed.

  Lemma pow_mod_1 :
    forall x,
      canonical x ->
      pow_mod x 1%nat = x.
  Proof.
    intros x Hx.
    simpl.
    apply mul_mod_one_r.
    exact Hx.
  Qed.

  Lemma pow_mod_2 :
    forall x,
      canonical x ->
      pow_mod x 2%nat = mul_mod x x.
  Proof.
    intros x Hx.
    simpl.
    rewrite mul_mod_one_r by exact Hx.
    reflexivity.
  Qed.

  Lemma pow_mod_3 :
    forall x,
      canonical x ->
      pow_mod x 3%nat = mul_mod (mul_mod x x) x.
  Proof.
    intros x Hx.
    simpl.
    rewrite mul_mod_one_r by exact Hx.
    reflexivity.
  Qed.

  Lemma twiddle_acc_pow_mod :
    forall n omega base (t : tree int n),
      twiddle_acc n omega (pow_mod omega base) t =
      (twiddle_from n omega base t, pow_mod omega (base + pow2 n)%nat).
  Proof.
    induction n as [|n IH]; intros omega base t.
    - simpl.
      rewrite Nat.add_1_r.
      reflexivity.
    - destruct t as [l r].
      simpl.
      rewrite IH.
      rewrite IH.
      rewrite pow2_succ.
      rewrite Nat.add_assoc.
      reflexivity.
  Qed.

  Lemma twiddle_tree_fast_eq :
    forall n omega (t : tree int n),
      twiddle_tree_fast n omega t = twiddle_tree n omega t.
  Proof.
    intros n omega t.
    unfold twiddle_tree_fast, twiddle_tree.
    change one with (pow_mod omega 0%nat).
    rewrite twiddle_acc_pow_mod.
    reflexivity.
  Qed.

  Lemma canonical_twiddle_acc :
    forall n omega w (t : tree int n),
      canonical omega ->
      canonical w ->
      canonical_tree n t ->
      canonical_tree n (fst (twiddle_acc n omega w t)) /\
      canonical (snd (twiddle_acc n omega w t)).
  Proof.
    induction n as [|n IH]; intros omega w t Homega Hw Ht.
    - simpl in *.
      split.
      + apply canonical_mul_mod.
      + apply canonical_mul_mod.
    - destruct t as [l r].
      simpl in Ht |- *.
      destruct Ht as [Hl Hr].
      destruct (twiddle_acc n omega w l) as [l1 w1] eqn:Hleft.
      destruct (IH omega w l Homega Hw Hl) as [Hcl Hcw1].
      rewrite Hleft in Hcl.
      rewrite Hleft in Hcw1.
      destruct (twiddle_acc n omega w1 r) as [r1 w2] eqn:Hright.
      destruct (IH omega w1 r Homega Hcw1 Hr) as [Hcr Hcw2].
      rewrite Hright in Hcr.
      rewrite Hright in Hcw2.
      cbn.
      split.
      + split; assumption.
      + exact Hcw2.
  Qed.

  Lemma twiddle_acc_u63_eq :
    forall n omega w (t : tree int n),
      canonical omega ->
      canonical w ->
      canonical_tree n t ->
      twiddle_acc_u63 n omega w t = twiddle_acc n omega w t.
  Proof.
    induction n as [|n IH]; intros omega w t Homega Hw Ht.
    - simpl in *.
      f_equal.
      + apply mul_mod_fast_eq; assumption.
      + apply mul_mod_fast_eq; assumption.
    - destruct t as [l r].
      simpl in Ht |- *.
      destruct Ht as [Hl Hr].
      rewrite IH by assumption.
      destruct (twiddle_acc n omega w l) as [l1 w1] eqn:Hleft.
      pose proof (canonical_twiddle_acc n omega w l Homega Hw Hl) as [_ Hcw1].
      rewrite Hleft in Hcw1.
      rewrite IH by assumption.
      reflexivity.
  Qed.

  Lemma twiddle_tree_u63_eq :
    forall n omega (t : tree int n),
      canonical omega ->
      canonical_tree n t ->
      twiddle_tree_u63 n omega t = twiddle_tree n omega t.
  Proof.
    intros n omega t Homega Ht.
    unfold twiddle_tree_u63.
    rewrite twiddle_acc_u63_eq.
    - apply twiddle_tree_fast_eq.
    - exact Homega.
    - apply canonical_one.
    - exact Ht.
  Qed.

  Lemma butterfly_tree_u63_eq :
    forall n (x y : tree int n),
      canonical_tree n x ->
      canonical_tree n y ->
      butterfly_tree_u63 n x y = butterfly_tree n x y.
  Proof.
    induction n as [|n IH]; intros x y Hx Hy.
    - simpl in *.
      f_equal.
      + apply add_mod_fast_eq; assumption.
      + apply sub_mod_fast_eq; assumption.
    - destruct x as [xl xr], y as [yl yr].
      simpl in Hx, Hy |- *.
      destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
      rewrite IH by assumption.
      rewrite IH by assumption.
      reflexivity.
  Qed.

  Lemma butterfly_tree_eq_zip :
    forall n (x y : tree int n),
      butterfly_tree n x y = (zip_tree n add_mod x y, zip_tree n sub_mod x y).
  Proof.
    induction n as [|n IH]; intros x y.
    - reflexivity.
    - destruct x as [xl xr], y as [yl yr].
      simpl.
      rewrite IH.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma twiddle_butterfly_acc_fuse :
    forall n omega w (x y : tree int n),
      twiddle_butterfly_acc n omega w x y =
      let '(ty, w1) := twiddle_acc_u63 n omega w y in
      let '(s, d) := butterfly_tree_u63 n x ty in
      ((s, d), w1).
  Proof.
    induction n as [|n IH]; intros omega w x y.
    - reflexivity.
    - destruct x as [xl xr], y as [yl yr].
      simpl.
      destruct (twiddle_acc_u63 n omega w yl) as [yl1 w1] eqn:Htwyl.
      destruct (butterfly_tree_u63 n xl yl1) as [sl dl] eqn:Hbfyl.
      destruct (twiddle_acc_u63 n omega w1 yr) as [yr1 w2] eqn:Htwyr.
      destruct (butterfly_tree_u63 n xr yr1) as [sr dr] eqn:Hbfyr.
      rewrite (IH omega w xl yl).
      rewrite Htwyl, Hbfyl.
      rewrite (IH omega w1 xr yr).
      rewrite Htwyr, Hbfyr.
      reflexivity.
  Qed.

  Lemma twiddle_butterfly_acc_eq :
    forall n omega w (x y : tree int n),
      canonical omega ->
      canonical w ->
      canonical_tree n x ->
      canonical_tree n y ->
      twiddle_butterfly_acc n omega w x y =
      let '(ty, w1) := twiddle_acc n omega w y in
      let '(s, d) := butterfly_tree n x ty in
      ((s, d), w1).
  Proof.
    intros n omega w x y Homega Hw Hx Hy.
    rewrite twiddle_butterfly_acc_fuse.
    rewrite twiddle_acc_u63_eq by assumption.
    destruct (twiddle_acc n omega w y) as [ty w1] eqn:Htw.
    simpl.
    pose proof (canonical_twiddle_acc n omega w y Homega Hw Hy) as [Hty _].
    rewrite Htw in Hty.
    rewrite butterfly_tree_u63_eq by assumption.
    reflexivity.
  Qed.

  Lemma ntt_fast_1_eq_with :
    forall rootf (t : tree int 1),
      canonical_tree 1 t ->
      ntt_fast_1 t = ntt_with rootf 1 t.
  Proof.
    intros rootf [a b] Ht.
    simpl in Ht.
    unfold ntt_fast_1, ntt_with, twiddle_tree.
    simpl.
    destruct Ht as [Ha Hb].
    rewrite mul_mod_one_r by exact Hb.
    f_equal.
    - apply add_mod_fast_eq; assumption.
    - apply sub_mod_fast_eq; assumption.
  Qed.

  Lemma canonical_ntt_fast_1 :
    forall (t : tree int 1),
      canonical_tree 1 t ->
      canonical_tree 1 (ntt_fast_1 t).
  Proof.
    intros [a b] Ht.
    simpl in Ht |- *.
    destruct Ht as [Ha Hb].
    split.
    - apply canonical_add_mod_fast; assumption.
    - apply canonical_sub_mod_fast; assumption.
  Qed.

  Lemma ntt_fast_2_with_eq :
    forall rootf,
      (forall n, canonical (rootf n)) ->
      forall (t : tree int 2),
        canonical_tree 2 t ->
        ntt_fast_2_with rootf t = ntt_with rootf 2 t.
  Proof.
    intros rootf Hroot [[a b] [c d]] Ht.
    simpl in Ht.
    destruct Ht as [[Ha Hb] [Hc Hd]].
    unfold ntt_fast_2_with, ntt_with, twiddle_tree.
    simpl.
    rewrite mul_mod_one_r by exact Hb.
    rewrite mul_mod_one_r by apply canonical_add_mod.
    rewrite mul_mod_one_r by exact Hd.
    set (l0f := add_mod_fast a b).
    set (l1f := sub_mod_fast a b).
    set (r0f := add_mod_fast c d).
    set (r1f := sub_mod_fast c d).
    assert (Hl0 : l0f = add_mod a b).
    {
      unfold l0f.
      apply add_mod_fast_eq; assumption.
    }
    assert (Hl1 : l1f = sub_mod a b).
    {
      unfold l1f.
      apply sub_mod_fast_eq; assumption.
    }
    assert (Hr0 : r0f = add_mod c d).
    {
      unfold r0f.
      apply add_mod_fast_eq; assumption.
    }
    assert (Hr1 : r1f = sub_mod c d).
    {
      unfold r1f.
      apply sub_mod_fast_eq; assumption.
    }
    rewrite Hl0, Hl1, Hr0, Hr1.
    rewrite mul_mod_fast_eq.
    2:{ apply Hroot. }
    2:{ apply canonical_sub_mod. }
    rewrite mul_mod_one_r by apply Hroot.
    rewrite add_mod_fast_eq.
    2:{ apply canonical_add_mod. }
    2:{ apply canonical_add_mod. }
    rewrite add_mod_fast_eq.
    2:{ apply canonical_sub_mod. }
    2:{ apply canonical_mul_mod. }
    rewrite sub_mod_fast_eq.
    2:{ apply canonical_add_mod. }
    2:{ apply canonical_add_mod. }
    rewrite sub_mod_fast_eq.
    2:{ apply canonical_sub_mod. }
    2:{ apply canonical_mul_mod. }
    reflexivity.
  Qed.

  Lemma canonical_ntt_fast_2_with :
    forall rootf,
      (forall n, canonical (rootf n)) ->
      forall (t : tree int 2),
        canonical_tree 2 t ->
        canonical_tree 2 (ntt_fast_2_with rootf t).
  Proof.
    intros rootf Hroot [[a b] [c d]] Ht.
    simpl in Ht |- *.
    destruct Ht as [[Ha Hb] [Hc Hd]].
    split.
    - split.
      + apply canonical_add_mod_fast.
        * apply canonical_add_mod_fast; assumption.
        * apply canonical_add_mod_fast; assumption.
      + apply canonical_add_mod_fast.
        * apply canonical_sub_mod_fast; assumption.
        * apply canonical_mul_mod_fast.
          -- apply Hroot.
          -- apply canonical_sub_mod_fast; assumption.
    - split.
      + apply canonical_sub_mod_fast.
        * apply canonical_add_mod_fast; assumption.
        * apply canonical_add_mod_fast; assumption.
      + apply canonical_sub_mod_fast.
        * apply canonical_sub_mod_fast; assumption.
        * apply canonical_mul_mod_fast.
          -- apply Hroot.
          -- apply canonical_sub_mod_fast; assumption.
  Qed.

  Lemma fst_twiddle_butterfly_acc_eq :
    forall n omega (x y : tree int n),
      canonical omega ->
      canonical_tree n x ->
      canonical_tree n y ->
      fst (twiddle_butterfly_acc n omega one x y) =
      butterfly_tree n x (twiddle_tree n omega y).
  Proof.
    intros n omega x y Homega Hx Hy.
    pose proof (twiddle_butterfly_acc_eq n omega one x y Homega canonical_one Hx Hy) as H.
    rewrite H.
    unfold twiddle_tree.
    change one with (pow_mod omega 0%nat).
    rewrite twiddle_acc_pow_mod.
    destruct (butterfly_tree n x (twiddle_from n omega 0 y)) as [s d].
    reflexivity.
  Qed.

  Lemma twiddle_butterfly_acc_eq_fst_let :
    forall n omega (x y : tree int n),
      canonical omega ->
      canonical_tree n x ->
      canonical_tree n y ->
      (let '((s, d), _) := twiddle_butterfly_acc n omega one x y in (s, d)) =
      butterfly_tree n x (twiddle_tree n omega y).
  Proof.
    intros n omega x y Homega Hx Hy.
    destruct (twiddle_butterfly_acc n omega one x y) as [[s d] w1] eqn:Hacc.
    simpl.
    pose proof (fst_twiddle_butterfly_acc_eq n omega x y Homega Hx Hy) as H.
    rewrite Hacc in H.
    exact H.
  Qed.

  Lemma ntt_fast_3_with_as_twiddle_butterfly :
    forall rootf,
      (forall n, canonical (rootf n)) ->
      forall (t : tree int 3),
        canonical_tree 3 t ->
        ntt_fast_3_with rootf t =
        let '(l, r) := t in
        let even_part := ntt_fast_2_with rootf l in
        let odd_part := ntt_fast_2_with rootf r in
        fst (twiddle_butterfly_acc 2%nat (rootf 3%nat) one even_part odd_part).
  Proof.
    intros rootf Hroot [l r] Ht.
    simpl in Ht.
    destruct Ht as [Hl Hr].
    unfold ntt_fast_3_with.
    remember (ntt_fast_2_with rootf l) as even eqn:Heven.
    remember (ntt_fast_2_with rootf r) as odd eqn:Hodd.
    assert (Hodd_can : canonical_tree 2 odd).
    {
      subst odd.
      apply canonical_ntt_fast_2_with; assumption.
    }
    destruct even as [[e0 e1] [e2 e3]], odd as [[o0 o1] [o2 o3]].
    simpl in Hodd_can |- *.
    destruct Hodd_can as [[Ho0 Ho1] [Ho2 Ho3]].
    rewrite mul_mod_fast_one_r by exact Ho0.
    rewrite mul_mod_fast_one_r by (apply Hroot).
    reflexivity.
  Qed.

  Lemma ntt_fast_3_with_eq :
    forall rootf,
      (forall n, canonical (rootf n)) ->
      forall (t : tree int 3),
        canonical_tree 3 t ->
        ntt_fast_3_with rootf t = ntt_with rootf 3 t.
  Proof.
    intros rootf Hroot [l r] Ht.
    simpl in Ht.
    destruct Ht as [Hl Hr].
    rewrite (ntt_fast_3_with_as_twiddle_butterfly rootf Hroot (l, r) (conj Hl Hr)).
    simpl (ntt_with rootf 3 (l, r)).
    rewrite fst_twiddle_butterfly_acc_eq.
    2:{ apply Hroot. }
    2:{ apply canonical_ntt_fast_2_with; assumption. }
    2:{ apply canonical_ntt_fast_2_with; assumption. }
    rewrite (ntt_fast_2_with_eq rootf Hroot l Hl).
    rewrite (ntt_fast_2_with_eq rootf Hroot r Hr).
    rewrite butterfly_tree_eq_zip.
    reflexivity.
  Qed.

  Lemma unpack_pack_block8 :
    forall (t : tree int 3),
      unpack_block8 (pack_block8 t) = t.
  Proof.
    intros [[[x0 x1] [x2 x3]] [[x4 x5] [x6 x7]]].
    reflexivity.
  Qed.

  Lemma unpack_pack_tree8 :
    forall k (t : tree int (S (S (S k)))),
      unpack_tree8 k (pack_tree8 k t) = t.
  Proof.
    induction k as [|k IH]; intros t.
    - apply unpack_pack_block8.
    - destruct t as [l r].
      simpl.
      rewrite IH.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma twiddle_butterfly_block8_eq :
    forall omega w x y,
      let '((s, d), w1) := twiddle_butterfly_block8 omega w x y in
      ((unpack_block8 s, unpack_block8 d), w1) =
      twiddle_butterfly_acc 3%nat omega w (unpack_block8 x) (unpack_block8 y).
  Proof.
    intros omega w x y.
    destruct x, y.
    reflexivity.
  Qed.

  Lemma twiddle_butterfly_acc_block8_eq :
    forall k omega w (x y : tree block8 k),
      let '((s, d), w1) := twiddle_butterfly_acc_block8 k omega w x y in
      ((unpack_tree8 k s, unpack_tree8 k d), w1) =
      twiddle_butterfly_acc (S (S (S k))) omega w (unpack_tree8 k x) (unpack_tree8 k y).
  Proof.
    induction k as [|k IH]; intros omega w x y.
    - apply twiddle_butterfly_block8_eq.
    - destruct x as [xl xr], y as [yl yr].
      cbn [twiddle_butterfly_acc_block8 unpack_tree8].
      change
        (twiddle_butterfly_acc (S (S (S (S k)))) omega w
           (unpack_tree8 (S k) (xl, xr)) (unpack_tree8 (S k) (yl, yr)))
        with
        (let '((sl', dl'), w1') :=
           twiddle_butterfly_acc (S (S (S k))) omega w
             (unpack_tree8 k xl) (unpack_tree8 k yl) in
         let '((sr', dr'), w2') :=
           twiddle_butterfly_acc (S (S (S k))) omega w1'
             (unpack_tree8 k xr) (unpack_tree8 k yr) in
         (((sl', sr'), (dl', dr')), w2')).
      destruct (twiddle_butterfly_acc_block8 k omega w xl yl) as [[sl dl] w1] eqn:Hleft.
      destruct (twiddle_butterfly_acc (S (S (S k))) omega w (unpack_tree8 k xl) (unpack_tree8 k yl))
        as [[sl' dl'] w1'] eqn:Hleft'.
      pose proof (IH omega w xl yl) as IHl.
      rewrite Hleft in IHl.
      rewrite Hleft' in IHl.
      inversion IHl; clear IHl; subst sl' dl' w1'.
      destruct (twiddle_butterfly_acc_block8 k omega w1 xr yr) as [[sr dr] w2] eqn:Hright.
      destruct (twiddle_butterfly_acc (S (S (S k))) omega w1 (unpack_tree8 k xr) (unpack_tree8 k yr))
        as [[sr' dr'] w2'] eqn:Hright'.
      pose proof (IH omega w1 xr yr) as IHr.
      rewrite Hright in IHr.
      rewrite Hright' in IHr.
      inversion IHr; clear IHr; subst sr' dr' w2'.
      change
        (twiddle_butterfly_acc (S (S (S (S k)))) omega w
           (unpack_tree8 k xl, unpack_tree8 k xr)
           (unpack_tree8 k yl, unpack_tree8 k yr))
        with
        (let '((sl', dl'), w1') :=
           twiddle_butterfly_acc (S (S (S k))) omega w
             (unpack_tree8 k xl) (unpack_tree8 k yl) in
         let '((sr', dr'), w2') :=
           twiddle_butterfly_acc (S (S (S k))) omega w1'
             (unpack_tree8 k xr) (unpack_tree8 k yr) in
         (((sl', sr'), (dl', dr')), w2')).
      rewrite Hleft'.
      rewrite Hright'.
      reflexivity.
  Qed.

  Lemma fst_twiddle_butterfly_acc_block8_eq :
    forall k omega w (x y : tree block8 k),
      unpack_tree8 (S k) (fst (twiddle_butterfly_acc_block8 k omega w x y)) =
      fst (twiddle_butterfly_acc (S (S (S k))) omega w (unpack_tree8 k x) (unpack_tree8 k y)).
  Proof.
    intros k omega w x y.
    destruct (twiddle_butterfly_acc_block8 k omega w x y) as [[s d] w1] eqn:Hacc.
    pose proof (twiddle_butterfly_acc_block8_eq k omega w x y) as H.
    rewrite Hacc in H.
    simpl in H.
    exact (f_equal fst H).
  Qed.

  Lemma ntt_fast_block8_ge3_with_eq_pairs :
    forall rootf k (t : tree block8 k),
      unpack_tree8 k (ntt_fast_block8_ge3_with rootf k t) =
      ntt_fast_pairs_ge3_with rootf k (unpack_tree8 k t).
  Proof.
    intros rootf k.
    induction k as [|k IH]; intros t.
    - destruct t.
      reflexivity.
    - destruct t as [l r].
      cbn [ntt_fast_block8_ge3_with ntt_fast_pairs_ge3_with].
      remember (ntt_fast_block8_ge3_with rootf k l) as even eqn:Heven.
      remember (ntt_fast_block8_ge3_with rootf k r) as odd eqn:Hodd.
      assert (Heven_eq :
        unpack_tree8 k even = ntt_fast_pairs_ge3_with rootf k (unpack_tree8 k l)).
      {
        subst even.
        apply IH.
      }
      assert (Hodd_eq :
        unpack_tree8 k odd = ntt_fast_pairs_ge3_with rootf k (unpack_tree8 k r)).
      {
        subst odd.
        apply IH.
      }
      rewrite fst_twiddle_butterfly_acc_block8_eq.
      rewrite Heven_eq.
      rewrite Hodd_eq.
      reflexivity.
  Qed.

  Lemma ntt_fast_record8_with_eq_pairs :
    forall rootf n (t : tree int n),
      ntt_fast_record8_with rootf n t = ntt_fast_pairs_with rootf n t.
  Proof.
    intros rootf n t.
    destruct n as [|[|[|k]]].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - simpl.
      rewrite ntt_fast_block8_ge3_with_eq_pairs.
      rewrite unpack_pack_tree8.
      reflexivity.
  Qed.

  Lemma output_get_zip_tree :
    forall n (f : int -> int -> int) (x y : tree int n) k,
      (k < pow2 n)%nat ->
      output_get n (zip_tree n f x y) k = f (output_get n x k) (output_get n y k).
  Proof.
    induction n as [|n IH]; intros f x y k Hk.
    - reflexivity.
    - destruct x as [xl xr], y as [yl yr].
      simpl in *.
      destruct (Nat.ltb_spec0 k (pow2 n)) as [Hlt|Hge].
      + apply IH.
        exact Hlt.
      + apply IH.
        rewrite pow2_succ in Hk.
        assert (Hsub : (Nat.sub k (pow2 n) < pow2 n)%nat) by lia.
        exact Hsub.
  Qed.

  Lemma input_get_map_tree :
    forall n (f : int -> int) (t : tree int n) i,
      (i < pow2 n)%nat ->
      input_get n (map_tree n f t) i = f (input_get n t i).
  Proof.
    induction n as [|n IH]; intros f t i Hi.
    - reflexivity.
    - destruct t as [l r].
      simpl in *.
      destruct (Nat.even i) eqn:Hev.
      + apply IH.
        assert (Heq : (i = 2 * Nat.div2 i)%nat).
        {
          apply Nat.even_spec in Hev.
          rewrite <- Nat.double_twice.
          apply Nat.Even_double.
          exact Hev.
        }
        rewrite pow2_succ in Hi.
        rewrite Heq in Hi.
        lia.
      + apply IH.
        assert (Heq : (i = S (2 * Nat.div2 i))%nat).
        {
          assert (Hodd : Nat.odd i = true).
          {
            rewrite <- Nat.negb_even.
            rewrite Hev.
            reflexivity.
          }
          apply Nat.odd_spec in Hodd.
          rewrite <- Nat.double_twice.
          apply Nat.Odd_double.
          exact Hodd.
        }
        rewrite pow2_succ in Hi.
        rewrite Heq in Hi.
        lia.
  Qed.

  Lemma output_get_twiddle_from :
    forall n omega base (t : tree int n) k,
      (k < pow2 n)%nat ->
      output_get n (twiddle_from n omega base t) k =
      mul_mod (pow_mod omega (Nat.add base k)) (output_get n t k).
  Proof.
    induction n as [|n IH]; intros omega base t k Hk.
    - simpl in Hk.
      apply Nat.lt_1_r in Hk.
      subst k.
      simpl.
      rewrite Nat.add_0_r.
      reflexivity.
    - destruct t as [l r].
      simpl in *.
      destruct (Nat.ltb_spec0 k (pow2 n)) as [Hlt|Hge].
      + rewrite IH by exact Hlt.
        reflexivity.
      + rewrite IH.
        2:{
          rewrite pow2_succ in Hk.
          assert (Hsub : (Nat.sub k (pow2 n) < pow2 n)%nat) by lia.
          exact Hsub.
        }
        replace (Nat.add (Nat.add base (pow2 n)) (Nat.sub k (pow2 n)))%nat
          with (Nat.add base k)%nat by lia.
        reflexivity.
  Qed.

  Lemma canonical_twiddle_from :
    forall n omega base (t : tree int n),
      canonical_tree n t ->
      canonical_tree n (twiddle_from n omega base t).
  Proof.
    induction n as [|n IH]; intros omega base t Hcanon.
    - simpl in *.
      apply canonical_mul_mod.
    - destruct t as [l r].
      simpl in *.
      destruct Hcanon as [Hl Hr].
      split.
      + apply IH.
        exact Hl.
      + apply IH.
        exact Hr.
  Qed.

  Lemma canonical_zip_add :
    forall n (x y : tree int n),
      canonical_tree n x ->
      canonical_tree n y ->
      canonical_tree n (zip_tree n add_mod x y).
  Proof.
    induction n as [|n IH]; intros x y Hx Hy.
    - simpl in *.
      apply canonical_add_mod.
    - destruct x as [xl xr], y as [yl yr].
      simpl in *.
      destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
      split.
      + apply IH; assumption.
      + apply IH; assumption.
  Qed.

  Lemma canonical_zip_sub :
    forall n (x y : tree int n),
      canonical_tree n x ->
      canonical_tree n y ->
      canonical_tree n (zip_tree n sub_mod x y).
  Proof.
    induction n as [|n IH]; intros x y Hx Hy.
    - simpl in *.
      apply canonical_sub_mod.
    - destruct x as [xl xr], y as [yl yr].
      simpl in *.
      destruct Hx as [Hxl Hxr], Hy as [Hyl Hyr].
      split.
      + apply IH; assumption.
      + apply IH; assumption.
  Qed.

  Lemma canonical_ntt_with :
    forall rootf n (t : tree int n),
      canonical_tree n t ->
      canonical_tree n (ntt_with rootf n t).
  Proof.
    induction n as [|n IH]; intros t Hcanon.
    - exact Hcanon.
    - destruct t as [l r].
      simpl in *.
      destruct Hcanon as [Hl Hr].
      split.
      + apply canonical_zip_add.
        * apply IH. exact Hl.
        * apply canonical_twiddle_from.
          apply IH. exact Hr.
      + apply canonical_zip_sub.
        * apply IH. exact Hl.
        * apply canonical_twiddle_from.
          apply IH. exact Hr.
  Qed.

  Lemma canonical_ntt :
    forall n (t : tree int n),
      canonical_tree n t ->
      canonical_tree n (ntt n t).
  Proof.
    induction n as [|n IH]; intros t Hcanon.
    - exact Hcanon.
    - destruct t as [l r].
      simpl in *.
      destruct Hcanon as [Hl Hr].
      apply conj.
      + apply canonical_zip_add.
        * apply IH. exact Hl.
        * apply canonical_twiddle_from.
          apply IH. exact Hr.
      + apply canonical_zip_sub.
        * apply IH. exact Hl.
        * apply canonical_twiddle_from.
          apply IH. exact Hr.
  Qed.

  Theorem ntt_correct :
    forall n (t : tree int n) k,
      canonical_tree n t ->
      (k < pow2 n)%nat ->
      value (output_get n (ntt n t) k) = dft n t k.
  Proof.
    induction n as [|n IH]; intros t k Hcanon Hk.
    - simpl.
      reflexivity.
    - destruct t as [l r].
      simpl in Hcanon.
      destruct Hcanon as [Hl Hr].
      simpl.
      destruct (Nat.ltb_spec0 k (pow2 n)) as [Hlt|Hge].
      + rewrite output_get_zip_tree by exact Hlt.
        rewrite value_add_mod.
        rewrite (IH l k Hl Hlt).
        unfold twiddle_tree.
        rewrite output_get_twiddle_from by exact Hlt.
        rewrite value_mul_mod.
        rewrite value_pow_mod.
        rewrite (IH r k Hr Hlt).
        reflexivity.
      + assert (Hsub : (Nat.sub k (pow2 n) < pow2 n)%nat).
        {
          rewrite pow2_succ in Hk.
          lia.
        }
        rewrite output_get_zip_tree by exact Hsub.
        rewrite value_sub_mod.
        rewrite (IH l (Nat.sub k (pow2 n)) Hl Hsub).
        unfold twiddle_tree.
        rewrite output_get_twiddle_from by exact Hsub.
        rewrite value_mul_mod.
        rewrite value_pow_mod.
        rewrite (IH r (Nat.sub k (pow2 n)) Hr Hsub).
        reflexivity.
  Qed.

  Lemma ntt_fast_pairs_ge3_with_eq :
    forall rootf,
      (forall n, canonical (rootf n)) ->
      forall k (t : tree int (S (S (S k)))),
        canonical_tree (S (S (S k))) t ->
        ntt_fast_pairs_ge3_with rootf k t = ntt_with rootf (S (S (S k))) t.
  Proof.
    intros rootf Hroot.
    induction k as [|k IH]; intros t Ht.
    - apply ntt_fast_3_with_eq; assumption.
    - destruct t as [l r].
      cbn [ntt_fast_pairs_ge3_with ntt_with] in Ht |- *.
      destruct Ht as [Hl Hr].
      rewrite IH by exact Hl.
      rewrite IH by exact Hr.
      replace
        (fst
           (twiddle_butterfly_acc (S (S (S k))) (rootf (S (S (S (S k))))) one
              (ntt_with rootf (S (S (S k))) l)
              (ntt_with rootf (S (S (S k))) r)))
        with
        (butterfly_tree (S (S (S k))) (ntt_with rootf (S (S (S k))) l)
           (twiddle_tree (S (S (S k))) (rootf (S (S (S (S k)))))
              (ntt_with rootf (S (S (S k))) r)))
        by (symmetry; apply fst_twiddle_butterfly_acc_eq;
            [apply Hroot | apply canonical_ntt_with; exact Hl | apply canonical_ntt_with; exact Hr]).
      rewrite butterfly_tree_eq_zip.
      reflexivity.
  Qed.

  Lemma ntt_fast_pairs_with_eq :
    forall rootf,
      (forall n, canonical (rootf n)) ->
      forall n (t : tree int n),
        canonical_tree n t ->
        ntt_fast_pairs_with rootf n t = ntt_with rootf n t.
  Proof.
    intros rootf Hroot n t Ht.
    destruct n as [|[|[|k]]].
    - reflexivity.
    - apply ntt_fast_1_eq_with.
      exact Ht.
    - apply ntt_fast_2_with_eq; assumption.
    - apply ntt_fast_pairs_ge3_with_eq; assumption.
  Qed.

  Lemma ntt_with_root_eq :
    forall n (t : tree int n),
      ntt_with root n t = ntt n t.
  Proof.
    induction n as [|n IH]; intros t.
    - reflexivity.
    - destruct t as [l r].
      simpl.
      rewrite IH.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma ntt_fast_block8_ge3_with_root_eq :
    forall k (t : tree block8 k),
      ntt_fast_block8_ge3_with root k t = ntt_fast_block8_ge3 k t.
  Proof.
    induction k as [|k IH]; intros t.
    - destruct t.
      reflexivity.
    - destruct t as [l r].
      simpl.
      rewrite IH.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma ntt_fast_record8_eq_with_root :
    forall n (t : tree int n),
      ntt_fast_record8 n t = ntt_fast_record8_with root n t.
  Proof.
    intros n t.
    destruct n as [|[|[|k]]].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - simpl.
      rewrite ntt_fast_block8_ge3_with_root_eq.
      reflexivity.
  Qed.

  Theorem ntt_fast_eq :
    forall n (t : tree int n),
      canonical_tree n t ->
      ntt_fast n t = ntt n t.
  Proof.
    intros n t Ht.
    unfold ntt_fast.
    rewrite ntt_fast_record8_eq_with_root.
    rewrite ntt_fast_record8_with_eq_pairs.
    rewrite ntt_fast_pairs_with_eq by (try apply canonical_root; exact Ht).
    apply ntt_with_root_eq.
  Qed.

  Theorem ntt_fast_correct :
    forall n (t : tree int n) k,
      canonical_tree n t ->
      (k < pow2 n)%nat ->
      value (output_get n (ntt_fast n t) k) = dft n t k.
  Proof.
    intros n t k Ht Hk.
    rewrite ntt_fast_eq by exact Ht.
    apply ntt_correct; assumption.
  Qed.

  Lemma canonical_intt_raw :
    forall n (t : tree int n),
      canonical_tree n t ->
      canonical_tree n (intt_raw n t).
  Proof.
    induction n as [|n IH]; intros t Ht.
    - exact Ht.
    - destruct t as [l r].
      simpl in Ht |- *.
      destruct Ht as [Hl Hr].
      split.
      + apply IH.
        apply canonical_zip_add; assumption.
      + apply IH.
        apply canonical_twiddle_from.
        apply canonical_zip_sub; assumption.
  Qed.

  Lemma intt_fast_tree_raw_eq :
    forall n (t : tree int n),
      canonical_tree n t ->
      intt_fast_tree_raw n t = intt_raw n t.
  Proof.
    induction n as [|n IH]; intros t Ht.
    - reflexivity.
    - destruct t as [l r].
      simpl in Ht |- *.
      destruct Ht as [Hl Hr].
      rewrite butterfly_tree_u63_eq by assumption.
      rewrite butterfly_tree_eq_zip.
      rewrite twiddle_tree_u63_eq.
      2:{ apply canonical_inv_root. }
      2:{ apply canonical_zip_sub; assumption. }
      rewrite IH.
      2:{ apply canonical_zip_add; assumption. }
      rewrite IH.
      2:{
        apply canonical_twiddle_from.
        apply canonical_zip_sub; assumption.
      }
      reflexivity.
  Qed.

  Lemma butterfly_twiddle_acc_tree_fuse :
    forall n omega w (x y : tree int n),
      butterfly_twiddle_acc_tree n omega w x y =
      let '(summed, diffed) := butterfly_tree_u63 n x y in
      let '(twiddled, w1) := twiddle_acc_u63 n omega w diffed in
      ((summed, twiddled), w1).
  Proof.
    induction n as [|n IH]; intros omega w x y.
    - reflexivity.
    - destruct x as [xl xr], y as [yl yr].
      simpl.
      destruct (butterfly_tree_u63 n xl yl) as [suml diffl] eqn:Hleft_bf.
      destruct (twiddle_acc_u63 n omega w diffl) as [twl w1] eqn:Hleft_tw.
      destruct (butterfly_tree_u63 n xr yr) as [sumr diffr] eqn:Hright_bf.
      destruct (twiddle_acc_u63 n omega w1 diffr) as [twr w2] eqn:Hright_tw.
      rewrite (IH omega w xl yl).
      rewrite Hleft_bf, Hleft_tw.
      rewrite (IH omega w1 xr yr).
      rewrite Hright_bf, Hright_tw.
      cbn [twiddle_acc_u63 butterfly_tree_u63].
      reflexivity.
  Qed.

  Lemma fst_butterfly_twiddle_acc_tree_eq :
    forall n omega (x y : tree int n),
      fst (butterfly_twiddle_acc_tree n omega one x y) =
      let '(summed, diffed) := butterfly_tree_u63 n x y in
      (summed, twiddle_tree_u63 n omega diffed).
  Proof.
    intros n omega x y.
    rewrite butterfly_twiddle_acc_tree_fuse.
    unfold twiddle_tree_u63.
    destruct (butterfly_tree_u63 n x y) as [summed diffed].
    destruct (twiddle_acc_u63 n omega one diffed) as [twiddled w1].
    reflexivity.
  Qed.

  Lemma butterfly_twiddle_block8_eq_tree :
    forall omega w x y,
      let '((s, d), w1) := butterfly_twiddle_block8 omega w x y in
      ((unpack_block8 s, unpack_block8 d), w1) =
      butterfly_twiddle_acc_tree 3%nat omega w (unpack_block8 x) (unpack_block8 y).
  Proof.
    intros omega w x y.
    destruct x, y.
    reflexivity.
  Qed.

  Lemma butterfly_twiddle_acc_block8_eq_tree :
    forall k omega w (x y : tree block8 k),
      let '((s, d), w1) := butterfly_twiddle_acc_block8 k omega w x y in
      ((unpack_tree8 k s, unpack_tree8 k d), w1) =
      butterfly_twiddle_acc_tree (S (S (S k))) omega w (unpack_tree8 k x) (unpack_tree8 k y).
  Proof.
    induction k as [|k IH]; intros omega w x y.
    - apply butterfly_twiddle_block8_eq_tree.
    - destruct x as [xl xr], y as [yl yr].
      cbn [butterfly_twiddle_acc_block8 unpack_tree8].
      change
        (butterfly_twiddle_acc_tree (S (S (S (S k)))) omega w
           (unpack_tree8 k xl, unpack_tree8 k xr)
           (unpack_tree8 k yl, unpack_tree8 k yr))
        with
        (let '((sl', dl'), w1') :=
           butterfly_twiddle_acc_tree (S (S (S k))) omega w
             (unpack_tree8 k xl) (unpack_tree8 k yl) in
         let '((sr', dr'), w2') :=
           butterfly_twiddle_acc_tree (S (S (S k))) omega w1'
             (unpack_tree8 k xr) (unpack_tree8 k yr) in
         (((sl', sr'), (dl', dr')), w2')).
      destruct (butterfly_twiddle_acc_block8 k omega w xl yl) as [[sl dl] w1] eqn:Hleft.
      destruct (butterfly_twiddle_acc_block8 k omega w1 xr yr) as [[sr dr] w2] eqn:Hright.
      assert (Hleft_tree :
        butterfly_twiddle_acc_tree (S (S (S k))) omega w
          (unpack_tree8 k xl) (unpack_tree8 k yl) =
        ((unpack_tree8 k sl, unpack_tree8 k dl), w1)).
      {
        pose proof (IH omega w xl yl) as H.
        rewrite Hleft in H.
        symmetry.
        exact H.
      }
      rewrite Hleft_tree.
      assert (Hright_tree :
        butterfly_twiddle_acc_tree (S (S (S k))) omega w1
          (unpack_tree8 k xr) (unpack_tree8 k yr) =
        ((unpack_tree8 k sr, unpack_tree8 k dr), w2)).
      {
        pose proof (IH omega w1 xr yr) as H.
        rewrite Hright in H.
        symmetry.
        exact H.
      }
      rewrite Hright_tree.
      reflexivity.
  Qed.

  Lemma fst_butterfly_twiddle_acc_block8_eq_tree :
    forall k omega (x y : tree block8 k),
      unpack_tree8 (S k) (fst (butterfly_twiddle_acc_block8 k omega one x y)) =
      fst (butterfly_twiddle_acc_tree (S (S (S k))) omega one (unpack_tree8 k x) (unpack_tree8 k y)).
  Proof.
    intros k omega x y.
    destruct (butterfly_twiddle_acc_block8 k omega one x y) as [[s d] w1] eqn:Hacc.
    pose proof (butterfly_twiddle_acc_block8_eq_tree k omega one x y) as H.
    rewrite Hacc in H.
    simpl in H.
    exact (f_equal fst H).
  Qed.

  Lemma intt_fast_block8_ge3_raw_eq_tree :
    forall k (t : tree block8 k),
      unpack_tree8 k (intt_fast_block8_ge3_raw k t) =
      intt_fast_tree_raw (S (S (S k))) (unpack_tree8 k t).
  Proof.
    induction k as [|k IH]; intros t.
    - destruct t.
      reflexivity.
    - destruct t as [l r].
      cbn [intt_fast_block8_ge3_raw unpack_tree8 intt_fast_tree_raw].
      destruct (butterfly_twiddle_acc_block8 k (inv_root (S (S (S (S k))))) one l r)
        as [[summed diffed] w1] eqn:Hacc.
      rewrite IH.
      rewrite IH.
      pose proof (fst_butterfly_twiddle_acc_block8_eq_tree k (inv_root (S (S (S (S k))))) l r) as Hfst.
      rewrite Hacc in Hfst.
      rewrite fst_butterfly_twiddle_acc_tree_eq in Hfst.
      destruct (butterfly_tree_u63 (S (S (S k))) (unpack_tree8 k l) (unpack_tree8 k r))
        as [summed' diffed'] eqn:Hbf.
      simpl in Hfst.
      inversion Hfst; clear Hfst; subst.
      reflexivity.
  Qed.

  Lemma intt_fast_record8_raw_eq :
    forall n (t : tree int n),
      canonical_tree n t ->
      intt_fast_record8_raw n t = intt_raw n t.
  Proof.
    intros n t Ht.
    destruct n as [|[|[|k]]].
    - reflexivity.
    - apply intt_fast_tree_raw_eq.
      exact Ht.
    - apply intt_fast_tree_raw_eq.
      exact Ht.
    - simpl.
      rewrite intt_fast_block8_ge3_raw_eq_tree.
      rewrite unpack_pack_tree8.
      change (intt_fast_tree_raw (S (S (S k))) t = intt_raw (S (S (S k))) t).
      apply intt_fast_tree_raw_eq.
      exact Ht.
  Qed.

  Theorem intt_fast_eq :
    forall n (t : tree int n),
      canonical_tree n t ->
      intt_fast n t = intt n t.
  Proof.
    intros n t Ht.
    unfold intt_fast, intt, intt_fast_record8.
    rewrite intt_fast_record8_raw_eq by exact Ht.
    rewrite scale_tree_fast_eq.
    - reflexivity.
    - apply canonical_inv_pow2.
    - apply canonical_intt_raw.
      exact Ht.
  Qed.

  Theorem intt_raw_correct_dif :
    forall n (t : tree int n) i,
      canonical_tree n t ->
      (i < pow2 n)%nat ->
      value (input_get n (intt_raw n t) i) = idft_dif_raw n t i.
  Proof.
    induction n as [|n IH]; intros t i Ht Hi.
    - reflexivity.
    - destruct t as [l r].
      simpl in Ht.
      destruct Ht as [Hl Hr].
      simpl.
      destruct (Nat.even i) eqn:Hev.
      + rewrite IH.
        2:{
          apply canonical_zip_add; assumption.
        }
        2:{
          assert (Heq : (i = 2 * Nat.div2 i)%nat).
          {
            apply Nat.even_spec in Hev.
            rewrite <- Nat.double_twice.
            apply Nat.Even_double.
            exact Hev.
          }
          rewrite pow2_succ in Hi.
          rewrite Heq in Hi.
          lia.
        }
        reflexivity.
      + rewrite IH.
        2:{
          apply canonical_twiddle_from.
          apply canonical_zip_sub; assumption.
        }
        2:{
          assert (Heq : (i = S (2 * Nat.div2 i))%nat).
          {
            assert (Hodd : Nat.odd i = true).
            {
              rewrite <- Nat.negb_even.
              rewrite Hev.
              reflexivity.
            }
            apply Nat.odd_spec in Hodd.
            rewrite <- Nat.double_twice.
            apply Nat.Odd_double.
            exact Hodd.
          }
          rewrite pow2_succ in Hi.
          rewrite Heq in Hi.
          lia.
        }
        reflexivity.
  Qed.

  Theorem intt_correct_dif :
    forall n (t : tree int n) i,
      canonical_tree n t ->
      (i < pow2 n)%nat ->
      value (input_get n (intt n t) i) = idft_dif n t i.
  Proof.
    intros n t i Ht Hi.
    unfold intt, idft_dif, scale_tree.
    rewrite input_get_map_tree by exact Hi.
    rewrite value_mul_mod.
    rewrite intt_raw_correct_dif by assumption.
    reflexivity.
  Qed.

  Theorem intt_fast_correct_dif :
    forall n (t : tree int n) i,
      canonical_tree n t ->
      (i < pow2 n)%nat ->
      value (input_get n (intt_fast n t) i) = idft_dif n t i.
  Proof.
    intros n t i Ht Hi.
    rewrite intt_fast_eq by exact Ht.
    apply intt_correct_dif; assumption.
  Qed.
End TreeNTT.
