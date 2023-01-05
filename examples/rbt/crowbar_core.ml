open! Core
include Crowbar

include Monad.Make (struct
  type 'a t = 'a gen

  let return = const
  let bind x ~f = dynamic_bind x f
  let map = `Define_using_bind
end)

let inc_range ~min ~max =
  with_printer pp_int
    (let open Let_syntax in
    let size = max - min in
    let%map i = range (size + 1) in
    i + min)
