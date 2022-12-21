open Rat
open Compilateur
open Exceptions

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

let pathFichiersRat = "../../../../../tests/projet/return/fichiersRat/"

(***********)
(*  TESTS  *)
(***********)


let%expect_test "testReturn0" =
  runtam (pathFichiersRat^"testReturn0.rat");
  [%expect{| 136 |}]

let%test_unit "testReturn1" =
try 
  let _ = runtam (pathFichiersRat^"testReturn1.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f1") -> ()

let%test_unit "testReturn2" =
  try 
    let _ = runtam (pathFichiersRat^"testReturn2.rat")
    in raise ErreurNonDetectee
  with
  | FonctionSansRetour("f2") -> ()

let%test_unit "testReturn3" =
try 
  let _ = runtam (pathFichiersRat^"testReturn3.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f3") -> ()

let%test_unit "testReturn3bis" =
try 
  let _ = runtam (pathFichiersRat^"testReturn3bis.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f3") -> ()

let%test_unit "testReturn3ter" =
try 
  let _ = runtam (pathFichiersRat^"testReturn3ter.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f3") -> ()

let%test_unit "testReturn4" =
try 
  let _ = runtam (pathFichiersRat^"testReturn4.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f4") -> ()

let%test_unit "testReturn4bis" =
try 
  let _ = runtam (pathFichiersRat^"testReturn4bis.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f4") -> ()

let%test_unit "testReturn5" =
try 
  let _ = runtam (pathFichiersRat^"testReturn5.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f5") -> ()

let%test_unit "testReturn6" =
try 
  let _ = runtam (pathFichiersRat^"testReturn6.rat")
  in raise ErreurNonDetectee
with
| FonctionSansRetour("f6") -> ()

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
