From Malfunction.Plugin Require Import Loader ZArith.

(* https://github.com/ocaml/Zarith/blob/master/z.mli *)

Axiom case : forall (A : Type), nat -> (unit -> A) -> (nat -> A) -> A.
Axiom nat_to_string : nat -> PrimString.string.

Verified Extract Constants [
  case => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.case",
  Nat.add => "Z.add",
  Nat.mul => "Z.mul",
  Nat.pow => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.pow",
  Nat.eqb => "Z.equal",
  Nat.max => "Z.max",
  Nat.min => "Z.min"
]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].

Verified Extract Inductives To Constants
  [ nat => [ [ ZArith.zero ZArith.succ | case ] ] ].

From Malfunction.Plugin Require Import OCamlFFI PrimString PrimInt63.
Set Verified Extraction Opam Path "/usr/local/bin/opam".

From MetaRocq Require Import Show.
From MetaRocq.Utils Require Import bytestring.
From Corelib Require Import PrimString.
Print Instances Show.

(* Verified Extract Constants [ *)
(*  nat_show => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.case" *)
(* ] *)


Verified Extract Constants [
    nat_to_string => "Z.to_string"
] Packages [ "zarith" ].

Definition string_of_pstring (s : string) : bytestring.string :=
  bytestring.String.concat bytestring.String.EmptyString (List.map char63_to_string (PrimStringAxioms.to_list s)).

(* Definition test_nat_zarith := *)
(*   print_endline ("Nat.pow 2 40 = " ++ string_of_pstring (nat_to_string (Nat.pow 2 40))). *)

(* Verified Extraction -fmt -compile-with-coq *)
(*   -unsafe extract-inductives *)
(*   -run test_nat_zarith "test_nat_zarith.mlf". *)
