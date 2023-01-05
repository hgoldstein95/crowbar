open! Core

module Let_syntax = struct
  type 'a t = 'a Crowbar.gen

  let return = Crowbar.const
  let bind g ~f = Crowbar.dynamic_bind g f
end

let find = Rbt.find ~compare:Int.compare
let insert = Rbt.insert ~compare:Int.compare
let invariant = Rbt.invariant ~compare:Int.compare

let cgen_rbt : (int, int) Rbt.t Crowbar.gen =
  let open Crowbar in
  let open Let_syntax in
  fix' ~init:5 (fun self n ->
      if n = 0 then return Rbt.E
      else
        choose
          [
            return Rbt.E;
            (let%bind rb = choose [ const Rbt.B; const Rbt.R ] in
             let%bind a = self (n - 1) in
             let%bind x = int in
             let%bind vx = int in
             let%bind b = self (n - 1) in
             return (Rbt.T (rb, a, x, vx, b)));
          ])

let cgen_rbt_bst : (int, int) Rbt.t Crowbar.gen =
  let open Crowbar in
  let open Let_syntax in
  fix' ~init:(1, 20) (fun self (lo, hi) ->
      if lo > hi then return Rbt.E
      else
        choose
          [
            return Rbt.E;
            (let%bind rb = choose [ const Rbt.B; const Rbt.R ] in
             let%bind x = range ~min:lo hi in
             let%bind a = self (lo, x - 1) in
             let%bind vx = int in
             let%bind b = self (x + 1, hi) in
             return (Rbt.T (rb, a, x, vx, b)));
          ])

let cgen_rbt_bst_bal : (int, int) Rbt.t Crowbar.gen =
  let open Crowbar in
  let open Let_syntax in
  let%bind bh = range ~min:1 4 in
  fix' ~init:(Rbt.R, bh, 1, 20) (fun self (prev_c, bh, lo, hi) ->
      if lo > hi || bh = 0 then return Rbt.E
      else
        let%bind rb =
          match prev_c with
          | Rbt.R -> return Rbt.B
          | Rbt.B -> choose [ const Rbt.B; const Rbt.R ]
        in
        let%bind x = range ~min:lo hi in
        let%bind a = self (rb, bh - 1, lo, x - 1) in
        let%bind vx = int in
        let%bind b = self (rb, bh - 1, x + 1, hi) in
        return (Rbt.T (rb, a, x, vx, b)))

let crowbar_insert_valid (t, k, v) =
  let open Crowbar in
  guard (invariant t);
  let t' = insert ~correct:false t ~key:k ~value:v in
  check (invariant t')

let () =
  let g =
    let open Crowbar in
    let open Let_syntax in
    let%bind t = cgen_rbt_bst_bal in
    let%bind k = range ~min:1 20 in
    let%bind v = range ~min:1 20 in
    return (t, k, v)
  in
  Crowbar.add_test ~name:"insert_valid" [ g ] crowbar_insert_valid

let crowbar_insert_post (t, k, k', v) =
  let open Crowbar in
  guard (invariant t);
  let t' = insert ~correct:false t ~key:k ~value:v in
  if k = k' then
    check_eq ~pp:(pp_option pp_int) ~eq:[%equal: int option] (find t' ~key:k')
      (Some v)
  else
    check_eq ~pp:(pp_option pp_int) ~eq:[%equal: int option] (find t' ~key:k')
      (find t ~key:k')

let () =
  let g =
    let open Crowbar in
    let open Let_syntax in
    let%bind t = cgen_rbt_bst_bal in
    let%bind k = range ~min:1 20 in
    let%bind k' = range ~min:1 20 in
    let%bind v = range ~min:1 20 in
    return (t, k, k', v)
  in
  Crowbar.add_test ~name:"insert_post" [ g ] crowbar_insert_post
