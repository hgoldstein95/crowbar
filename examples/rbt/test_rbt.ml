open! Core
module Crowbar = Crowbar_core

let find = Rbt.find ~compare:Int.compare
let insert = Rbt.insert ~compare:Int.compare
let invariant = Rbt.invariant ~compare:Int.compare

let pp_rbt ppf t =
  let rbt_to_string rbt = [%sexp_of: (int, int) Rbt.t] rbt |> Sexp.to_string in
  Format.fprintf ppf "%s" (rbt_to_string t)

let pp_color ppf = function
  | Rbt.R -> Format.fprintf ppf "R"
  | Rbt.B -> Format.fprintf ppf "B"

module Gen_rbt = struct
  let color =
    Crowbar.(with_printer pp_color (choose [ const Rbt.B; const Rbt.R ]))

  let naive : (int, int) Rbt.t Crowbar.gen =
    let open Crowbar in
    fix' ~init:5 (fun self n ->
        if n = 0 then return Rbt.E
        else
          choose
            [
              return Rbt.E;
              (let open Crowbar.Let_syntax in
              let%bind rb = color in
              let%bind x = int in
              let%bind vx = int in
              let%bind a = self (n - 1) in
              let%bind b = self (n - 1) in
              return (Rbt.T (rb, a, x, vx, b)));
            ])
    |> with_printer pp_rbt

  let with_bst_invariant : (int, int) Rbt.t Crowbar.gen =
    let open Crowbar in
    fix' ~init:(1, 20) (fun self (lo, hi) ->
        if lo > hi then return Rbt.E
        else
          choose
            [
              return Rbt.E;
              (let open Crowbar.Let_syntax in
              let%bind rb = color in
              let%bind x = inc_range ~min:lo ~max:hi in
              let%bind vx = int in
              let%bind a = self (lo, x - 1) in
              let%bind b = self (x + 1, hi) in
              return (Rbt.T (rb, a, x, vx, b)));
            ])
    |> with_printer pp_rbt

  let with_bh_invariant : (int, int) Rbt.t Crowbar.gen =
    let open Crowbar in
    let open Crowbar.Let_syntax in
    let%bind bh = inc_range ~min:1 ~max:4 in
    fix' ~init:(Rbt.R, bh) (fun self (parent_rb, bh) ->
        if bh = 0 then return Rbt.E
        else
          let%bind rb =
            match parent_rb with Rbt.R -> return Rbt.B | Rbt.B -> color
          in
          let new_bh = match parent_rb with Rbt.R -> bh | Rbt.B -> bh - 1 in
          let%bind x = inc_range ~min:1 ~max:20 in
          let%bind vx = int in
          let%bind a = self (rb, new_bh) in
          let%bind b = self (rb, new_bh) in
          return (Rbt.T (rb, a, x, vx, b)))
    |> with_printer pp_rbt

  let with_rbt_invariant : (int, int) Rbt.t Crowbar.gen =
    let open Crowbar in
    let open Crowbar.Let_syntax in
    let%bind bh = inc_range ~min:1 ~max:4 in
    fix' ~init:(Rbt.R, bh, 1, 20) (fun self (parent_rb, bh, lo, hi) ->
        if lo > hi || bh = 0 then return Rbt.E
        else
          let%bind rb =
            match parent_rb with Rbt.R -> return Rbt.B | Rbt.B -> color
          in
          let new_bh = match parent_rb with Rbt.R -> bh | Rbt.B -> bh - 1 in
          let%bind x = inc_range ~min:lo ~max:hi in
          let%bind vx = int in
          let%bind a = self (rb, new_bh, lo, x - 1) in
          let%bind b = self (rb, new_bh, x + 1, hi) in
          return (Rbt.T (rb, a, x, vx, b)))
    |> with_printer pp_rbt
end

let prop_insert_valid (t, k, v) =
  let open Crowbar in
  guard (invariant t);
  let t' = insert ~correct:false t ~key:k ~value:v in
  check (invariant t')

let prop_insert_post (t, k, k', v) =
  let open Crowbar in
  guard (invariant t);
  let t' = insert ~correct:false t ~key:k ~value:v in
  check_eq ~pp:(pp_option pp_int) ~eq:[%equal: int option] (find t' ~key:k')
    (if k = k' then Some v else find t ~key:k')

let gen = Gen_rbt.with_bst_invariant

let () =
  let g =
    let open Crowbar.Let_syntax in
    let%bind t = gen in
    let%bind k = Crowbar.inc_range ~min:1 ~max:20 in
    let%bind v = Crowbar.int in
    return (t, k, v)
  in
  Crowbar.add_test ~name:"insert_valid" [ g ] prop_insert_valid

let () =
  let g =
    let open Crowbar.Let_syntax in
    let%bind t = gen in
    let%bind k = Crowbar.inc_range ~min:1 ~max:20 in
    let%bind k' = Crowbar.inc_range ~min:1 ~max:20 in
    let%bind v = Crowbar.int in
    return (t, k, k', v)
  in
  Crowbar.add_test ~name:"insert_post" [ g ] prop_insert_post
