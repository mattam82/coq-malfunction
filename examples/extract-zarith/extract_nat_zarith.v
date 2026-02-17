Require Import Arith.

From Malfunction.Plugin Require Import Extract OCamlFFI.
(* From VerifiedExtraction Require Import Extraction OCamlFFI. *)
Set Verified Extraction Build Directory ".".

From MetaRocq.Utils Require Import bytestring.

(* This only interfaces with primitive integers, so no particular wrapping is needed. *)
(* However the polymorphic functions HAVE TO be masked to remove type argument
  applications, hence typed erasure is required. *)

Axiom bigzero : nat.
Axiom bigsucc : nat -> nat.
Axiom bigcase : forall (A : Type), nat -> (unit -> A) -> (nat -> A) -> A.
Axiom bigadd : nat -> nat -> nat.
Axiom bigmul : nat -> nat -> nat.
Axiom bigpow : nat -> nat -> nat.
Axiom bigequal : nat -> nat -> bool.
Verified Extract Constants [
  bigzero => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.zero",
  bigsucc => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.succ",
  bigcase => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.case",

  bigadd => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.add",
  bigmul => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.mul",
  bigpow => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.pow",

  bigequal => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.equal"
  ]
Packages [ "rocq_verified_extraction_ocaml_ffi" ].

Verified Extract Inductives To Constants
  [ nat => [ [ bigzero bigsucc | bigcase ] ] ].

Definition foo (x : nat) :=
  match x + 1 with
  | 0 => true
  | S _ => false
  end.

Definition test := foo 1.
Eval compute in test.
From MetaRocq Require Import Show.
Definition show_test :=
  let bz := bigzero in
  let bs := bigsucc in
  let bc := bigcase in
  print_string (show test).
MetaRocq Run Print mli show_test.

Set Verified Extraction Opam Path "/usr/local/bin/opam".

Verified Extraction -fmt -compile-with-coq
  -unsafe extract-inductives
  -run show_test "extract_nat_zarith.mlf".

Definition show_test2 :=
  let bz := bigzero in
  let bs := bigsucc in
  let bc := bigcase in
  let test := bigpow 2 30 in
  print_string (show (Nat.eqb test test)).
  (* print_string (show test). *)

Verified Extraction -fmt -compile-with-coq
  -unsafe extract-inductives
  -run show_test2 "extract_nat_zarith2.mlf".

Definition show_test2_bigeq :=
  let bz := bigzero in
  let bs := bigsucc in
  let bc := bigcase in
  let test := bigpow 2 30 in
  print_string (show (bigequal test test)).

(* Fail Timeout 1 Eval vm_compute in show_test2. *)

(* Verified Extract Constants [ *)
(*   Nat.add => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.add", *)
(*   Nat.mul => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.mul" ]. *)

Verified Extraction -fmt -compile-with-coq -time
  -unsafe extract-inductives
  -run show_test2_bigeq "extract_nat_zarith_bigeq.mlf".

(* Rebinding Nat.add, Nat.mul and Nat.pow to zarith *)

Definition show_test3_bigeq :=
  let test := Nat.pow 2 30 in
  print_string (show (Nat.eqb test test)).

Verified Extract Constants [
  Nat.add => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.add",
  Nat.mul => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.mul",
  Nat.pow => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.pow",
  Nat.eqb => "Rocq_verified_extraction_ocaml_ffi__Zarith_nat.equal" ].

Timeout 1 Verified Extraction -fmt -compile-with-coq -time
  -unsafe extract-inductives
  -run show_test3_bigeq "extract_nat_zarith_bigpow_bigeq.mlf".
