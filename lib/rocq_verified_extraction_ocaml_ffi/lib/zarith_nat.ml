(** Bindings to zarith GMP integers *)
type t = Z.t

let zero = Z.zero

let succ = Z.succ

let case discr zerob succb =
  if Z.equal zero discr then zerob () else succb (Z.pred discr)

let pow x exp =
  let exp = try Z.to_int exp with Z.Overflow -> raise (Invalid_argument "zarith's Z.pow is called with too large an exponent") in
  Z.pow x exp

let add = Z.add
let mul = Z.mul
let equal = Z.equal
