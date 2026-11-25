# 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC halts

`Final.v` proves `halts tm c0`: started on a blank tape, this machine halts. It does so after
346,613,804,468,191,894,895,080,818,748,230,768,977,389 (about 3.47·10^41) steps, but the step count is not part
of the Coq statement.

## The argument

**Visits.** Write A(a, b) for the configuration `0^∞ 1^a 0 C> 1^b 0^∞`. `Rules.v` proves, on the tape, that blank
tape reaches A(2, 9) (`start`) and that from a visit A(a, b) the machine reaches the next visit given by the map
`op` of `Visits.v`:

    b = 3                halt (11 steps later)
    b = 2                A(a - 3, 7)
    a >= b               A(a - b + 1, 2b + 3)          "swap"
    b = a + 1            A(4, 2a + 4)
    b = a + 2            A(1, 2a + 7)
    a even               A(2a + 4, b - a - 1)          "grow"
    a odd, b = a + 3     A(2a + 1, 9)
    a odd                A(2a + 3, b - a)              "grow"

so `halts_of_orbit`: if `opIter k (2, 9) = Some (a, 3)` for some k, the machine halts.

**The orbit.** The orbit of `op` from (2, 9) reaches (139754396279488, 139754396279492) at visit
79,859,656,218,973 (a even, b - a = 4), and (279508792558980, 3) at visit 79,859,656,218,974. Following
8·10^13 visits needs a fast checker:

- `Check.v` follows the visits in 63-bit machine integers (`Uint63`), one at a time (`ex1`) or in blocks of
  K = 12, 24 or 36 visits (`blk`). Away from the diagonal, `op` is a doubling map on d / s (d = b - a, s = a + b):
  grow and swap are its two digits. A block guesses its K digits as the top bits of b / s, applies them formally
  with a table of 12-digit chunks (`TP`, 16384 entries), and is kept only if both final coordinates are at least
  16·2^K. A refused block is redone one visit at a time.
- `J000.v` ... `J399.v` check the orbit in 400 segments of 2·10^11 visits (the last one shorter, ending at the
  halt) with `native_compute`: each states `seg p n a b a' b' = true` (n visits from (a, b) end at (a', b')), or
  `seg_halt` for the last.

**Soundness**, all without `native_compute`:

- `Block.v`, `block_ok`: for *any* list of digits, if their formal run from a visit ends with both coordinates at
  least 16·2^K, it is the next K visits of `op`. So the guess of the digits never needs to be right.
- `Tab.v`: the table holds, for each 12-digit chunk and low state, what the formal run of the chunk does
  (`chunk_inv` for all digit lists; the 16384 entries are checked with `vm_compute`).
- `Arith.v`, `Blk.v`, `BlkOk.v`: the 63-bit arithmetic of `blk` is exact or tracked modulo 2^63 where it can
  wrap, and `blk_ok`: an accepted block is K visits of `op`.
- `Ex1.v`, `ex1_ok`: `ex1` is `op`.
- `Run.v`, `seg_ok` and `seg_halt_ok`: `seg ... = true` gives `opIter n (a, b) = Some (a', b')`.
- `Final.v` chains the 400 segments with `opIter_add` and applies `halts_of_orbit`.

The rules on A(a, b) are due to the bbchallenge wiki; the orbit was first followed in C (see
busy-beaver-explorer, holdouts/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC), where it was also re-run one visit at a
time with exact step counts.

## Building

Run `M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC/build.sh` from `verify/` after `make`. It needs Coq 8.20 built with
the native compiler. Everything except the segments takes a few minutes. Each segment takes about 37 minutes, so the
400 segments are about 250 core-hours; they are independent, and `JOBS` sets how many run at once.

## Checked

All 400 segments were checked with Coq 8.20.1 (native compiler), each in 15 to 50 minutes, and `Final.v` compiles.
`Print Assumptions halts_tm` lists only the axioms of Coq's primitive 63-bit integers and arrays (`PrimInt63.*`,
`Uint63.*_spec`, `PArray.*`); the segments also trust `native_compute`.
