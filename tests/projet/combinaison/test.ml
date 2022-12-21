open Rat
open Compilateur
(* open Exceptions *)

(************************************************)
(*      Tests de plusieurs combinaisons de      *)
(* fonctionnalités rajoutées au cours du projet *)
(************************************************)

exception ErreurNonDetectee

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../../../../tests/runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let (tamfile, chan) = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;    (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile =
  print_string (runtamcode runtamcmde ratfile)

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/projet/combinaison/fichiersRat/"

(***********)
(*  TESTS  *)
(***********)

let%expect_test "testCombinaison1" =
  runtam (pathFichiersRat^"testCombinaison1.rat");
  [%expect{| 01010101018880101010101 |}]

let%expect_test "testCombinaison2" =
  runtam (pathFichiersRat^"testCombinaison2.rat");
  [%expect{| 56120 |}]

(*
let%test_unit "testfun5" =
  try 
    let _ = runtam (pathFichiersRat^"testfun5.rat")
    in raise ErreurNonDetectee
  with
  | FonctionSansRetour("f1") -> ()
*)


(* Fichiers de tests de la génération de code -> doivent passer la TDS *)
open Unix
open Filename

let rec test d p_tam = 
  try 
    let file = readdir d in
    if (check_suffix file ".rat") 
    then
    (
     try
       let _ = compiler  (p_tam^file) in (); 
     with e -> print_string (p_tam^file); print_newline(); raise e;
    )
    else ();
    test d p_tam
  with End_of_file -> ()

let%test_unit "all_tam" =
  let p_tam = "../../../../../tests/tam/sans_fonction/fichiersRat/" in
  let d = opendir p_tam in
  test d p_tam
