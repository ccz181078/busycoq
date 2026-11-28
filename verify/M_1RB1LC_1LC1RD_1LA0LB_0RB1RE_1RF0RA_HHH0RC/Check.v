(** The orbit checker for 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC: the visits A(a, b) followed in 63-bit
    machine integers, one at a time ([ex1]) or in blocks of K = 12, 24 or 36 visits ([blk]).

    Write s = a + b. Away from the diagonal, a visit either grows ((a, b) -> (2a + 4, b - a - 1) for a even,
    (2a + 3, b - a) for a odd; digit 1) or swaps ((a, b) -> (a - b + 1, 2b + 3); digit 0). The digits of a block
    are guessed as the K top bits Q of b / s; the K formal steps of those digits are applied in three (or two, or
    one) table lookups of 12 digits each ([chunk]); the block is kept only if both final coordinates are at least
    16 * 2^K, which makes the K visits that formal run whatever the guess was (Soundness.v).  A refused block is
    redone one visit at a time. *)
From Coq Require Import Uint63 PArray Bool PArith.
Local Open Scope uint63_scope.

(** One visit of the rules, for b <> 3 (b = 3 is the halt). *)
Definition ex1 (a b : int) : int * int :=
  if b =? 2 then (if a <? 3 then 0 else a - 3, 7) else
  if b <=? a then (a - b + 1, 2 * b + 3) else
  if b =? a + 1 then (4, 2 * a + 4) else
  if b =? a + 2 then (1, 2 * a + 7) else
  if is_even a then (2 * a + 4, b - a - 1) else
  if b =? a + 3 then (2 * a + 1, 9) else (2 * a + 3, b - a).

(** [k] visits one at a time, stopping at a halt (b = 3); the visit index [i] counts along. *)
Fixpoint exn (k : nat) (i a b : int) : int * int * int :=
  match k with
  | O => (i, a, b)
  | S k => if b =? 3 then (i, a, b) else let (a', b') := ex1 a b in exn k (i + 1) a' b'
  end.

(** The 12-digit table. From the low state st = (a mod 2) + 2 (s mod 2) and the digits bt (12 bits, most
    significant first): the formal run takes d = b - a and s to 2^12 d - s (2 bt - 4095) + q and s + ds, and
    the low state to st'. *)
Fixpoint tab_go (n : nat) (bt i ap sp q ds : int) : int * int * int :=
  match n with
  | O => (q, ds, ap lor (sp << 1))
  | S n =>
    if (bt >> (11 - i)) land 1 =? 1
    then tab_go n bt (i + 1) ap (sp lxor 1) (2 * q + (if ap =? 1 then 0 - 3 else 0 - 5) - ds) (ds + 3)
    else tab_go n bt (i + 1) ((sp + 1) land 1) sp (2 * q + 2 + ds) (ds + 4)
  end.
Definition tabent (k : int) : int * int * int := tab_go 12 (k land 4095) 0 ((k >> 12) land 1) (k >> 13) 0 0.
(** packed: (q + 2^30) * 2^8 + ds * 4 + st' *)
Definition pack (e : int * int * int) : int :=
  let '(q, ds, st) := e in ((q + (1 << 30)) << 8) lor (ds << 2) lor st.
Fixpoint fill (n : nat) (k : int) (t : array int) : array int :=
  match n with O => t | S n => fill n (k + 1) (t.[k <- pack (tabent k)]) end.
Definition TP : array int := fill 16384 0 (make 16384 0).

(** One chunk of 12 digits of Q, at shift sh: new low state, offset of s, correction E. *)
Definition chunk (tp : array int) (Q sh st off E : int) : int * int * int :=
  let bt := (Q >> sh) land 4095 in
  let v := tp.[(st << 12) + bt] in
  (v land 3, off + ((v >> 2) land 63), E + ((off * (2 * bt - 4095) - ((v >> 8) - (1 << 30))) << sh)).

(** A block of K visits (K = 12, 24 or 36) from (a, b); (0, 0) if refused. *)
Definition blk (tp : array int) (K a b : int) : int * int :=
  let s := a + b in
  let Q0 := if K =? 12 then (b << 12) / s else (b << 13) / ((s >> (K - 13)) + 1) in
  let Q := Q0 + ((b << K) - s * Q0) / s in
  let '(h, l) := mulc s Q in
  let nl := b << K in
  if (Q <? 1 << K) && (h =? b >> (63 - K)) && (l <=? nl) && (nl - l <? s) then
    let rem := nl - l in
    let st0 := (a land 1) + ((s land 1) << 1) in
    let '(st1, off1, E1) := chunk tp Q (K - 12) st0 0 0 in
    let '(st2, off2, E2) := if K =? 12 then (st1, off1, E1) else chunk tp Q (K - 24) st1 off1 E1 in
    let '(_, off, E) := if K =? 36 then chunk tp Q 0 st2 off2 E2 else (st2, off2, E2) in
    let sK := s + off in
    let b2 := sK + 2 * rem - s - E in
    let a2 := 2 * sK - b2 in
    let G := 32 << K in
    if (G <=? a2) && (G <=? b2) && (a2 <? 1 << 62) && (b2 <? 1 << 62) then (a2 >> 1, b2 >> 1) else (0, 0)
  else (0, 0).

(** The block length for a + b = s. *)
Definition kof (s : int) : int :=
  if 1 << 46 <=? s then 36 else if 1 << 34 <=? s then 24 else if 1 << 22 <=? s then 12 else 0.
Definition knat (K : int) : nat := if K =? 36 then 36 else if K =? 24 then 24 else 12.

(** Stop at visit n, at the halt, or if a coordinate gets too large for the arithmetic above. *)
Definition stop (n i a b : int) : bool := (i =? n) || (b =? 3) || (1 << 56 <=? a) || (1 << 56 <=? b).

Definition one (tp : array int) (n i a b : int) : int * int * int :=
  if stop n i a b then (i, a, b) else
  let K := kof (a + b) in
  if (K =? 0) || (n - i <? K) then exn 1 i a b else
  let '(a', b') := blk tp K a b in
  if a' =? 0 then exn (knat K) i a b else (i + K, a', b').

Fixpoint run (tp : array int) (p : positive) (n i a b : int) : int * int * int :=
  if stop n i a b then (i, a, b) else
  match p with
  | xH => one tp n i a b
  | xO p => let '(i, a, b) := run tp p n i a b in run tp p n i a b
  | xI p => let '(i, a, b) := run tp p n i a b in let '(i, a, b) := run tp p n i a b in one tp n i a b
  end.

(** n visits from (a, b) end at (a', b'). *)
Definition seg (p : positive) (n a b a' b' : int) : bool :=
  let '(i, x, y) := run TP p n 0 a b in (i =? n) && (x =? a') && (y =? b').
(** The h-th visit from (a, b) is the halting visit (a', 3). *)
Definition seg_halt (p : positive) (h a b a' : int) : bool :=
  let '(i, x, y) := run TP p h 0 a b in (i =? h) && (x =? a') && (y =? 3).
