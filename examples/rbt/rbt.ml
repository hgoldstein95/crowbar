open! Core

type color = R | B [@@deriving sexp, equal, compare, quickcheck]

type ('k, 'v) t = E | T of color * ('k, 'v) t * 'k * 'v * ('k, 'v) t
[@@deriving sexp, equal, compare, quickcheck]

let empty = E

let rec every p = function
  | E -> true
  | T (_, a, x, _, b) -> p x && every p a && every p b

let rec is_bst (tree : ('k, 'v) t) ~(compare : 'k -> 'k -> int) : bool =
  match tree with
  | E -> true
  | T (_, a, x, _, b) ->
      every (fun y -> compare y x < 0) a
      && every (fun y -> compare y x > 0) b
      && is_bst ~compare a && is_bst ~compare b

let consistent_black_height (tree : ('k, 'v) t) : bool =
  let rec loop = function
    | E -> (true, 1)
    | T (rb, a, _, _, b) ->
        let a_b, a_h = loop a in
        let b_b, b_h = loop b in
        (a_b && b_b && a_h = b_h, a_h + if [%equal: color] rb B then 1 else 0)
  in
  fst (loop tree)

let rec no_red_red (tree : ('k, 'v) t) : bool =
  match tree with
  | E -> true
  | T (B, a, _, _, b) -> no_red_red a && no_red_red b
  | T (R, a, _, _, b) ->
      let black_root = function T (R, _, _, _, _) -> false | _ -> true in
      black_root a && black_root b && no_red_red a && no_red_red b

let invariant (tree : ('k, 'v) t) ~(compare : 'k -> 'k -> int) : bool =
  is_bst ~compare tree && consistent_black_height tree && no_red_red tree

let balance ?(correct = true) (rb : color) (a : ('k, 'v) t) (x : 'k) (vx : 'v)
    (b : ('k, 'v) t) : ('k, 'v) t =
  match (rb, a, x, vx, b) with
  | B, T (R, T (R, a, x, vx, b), y, vy, c), z, vz, d
  | B, T (R, a, x, vx, T (R, b, y, vy, c)), z, vz, d
  | B, a, x, vx, T (R, b, y, vy, T (R, c, z, vz, d)) ->
      if correct then T (R, T (B, a, x, vx, b), y, vy, T (B, c, z, vz, d))
      else T (R, T (B, a, x, vx, c), y, vy, T (B, b, z, vz, d))
  | B, a, x, vx, T (R, T (R, b, y, vy, c), z, vz, d) ->
      T (R, T (B, a, x, vx, b), y, vy, T (B, c, z, vz, d))
  | _ -> T (rb, a, x, vx, b)

let blacken = function E -> E | T (_, a, x, vx, b) -> T (B, a, x, vx, b)

let insert ?(correct = true) (tree : ('k, 'v) t) ~(compare : 'k -> 'k -> int)
    ~(key : 'k) ~(value : 'v) : ('k, 'v) t =
  let rec loop x vx = function
    | E -> T (R, E, x, vx, E)
    | T (rb, a, y, vy, b) ->
        let c = compare x y in
        if c < 0 then balance ~correct rb (loop x vx a) y vy b
        else if c > 0 then balance ~correct rb a y vy (loop x vx b)
        else T (rb, a, x, vx, b)
  in
  blacken (loop key value tree)

let find (tree : ('k, 'v) t) ~(compare : 'k -> 'k -> int) ~(key : 'k) :
    'v option =
  let rec loop = function
    | E -> None
    | T (_, a, y, vy, b) ->
        let c = compare key y in
        if c < 0 then loop a else if c > 0 then loop b else Some vy
  in
  loop tree