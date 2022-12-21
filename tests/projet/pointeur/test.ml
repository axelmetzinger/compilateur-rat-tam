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

let pathFichiersRat = "../../../../../tests/projet/pointeur/fichiersRat/"

(***********)
(*  TESTS  *)
(***********)

let%expect_test "testPointeur1" =
  runtam (pathFichiersRat^"testPointeur1.rat");
  [%expect{| 423 |}]

let%expect_test "testPointeur2" =
  runtam (pathFichiersRat^"testPointeur2.rat");
  [%expect{| false |}]

let%expect_test "testPointeur3" =
  runtam (pathFichiersRat^"testPointeur3.rat");
  [%expect{| [3/4] |}]

let%expect_test "testPointeur4" =
  runtam (pathFichiersRat^"testPointeur4.rat");
  [%expect{| 0x10x10x20x2555 |}]

let%expect_test "testPointeur5" =
  runtam (pathFichiersRat^"testPointeur5.rat");
  [%expect{| 0x30x30x10x1[1/2] |}]

let%expect_test "testPointeur6" =
  runtam (pathFichiersRat^"testPointeur6.rat");
  [%expect{| 0x00x10485750x1048573[3/4]0x10x1048571[1/2] |}]

let%expect_test "testPointeur7" =
  runtam (pathFichiersRat^"testPointeur7.rat");
  [%expect{| [1/2] |}]

let%expect_test "testPointeur8" =
  runtam (pathFichiersRat^"testPointeur8.rat");
  [%expect{| [1/2][3/4] |}]

(* Test de l'affichage des adresses des variables et des pointeurs
   Ce test n'est possible ici que parceque l'adresse de base du tas est
   toujours la même (0x1048575 puis se décrémente).
   Tester cela dans des conditions réels sur une machine et un système classique
   est impossible, car l'adresse de base du tas est attribuée de manière `aléatoire`
   par le système au lancement du processus. *)
let%expect_test "testPointeur9" =
  runtam (pathFichiersRat^"testPointeur9.rat");
  [%expect{| 0x00x10485750x1048573[1/2]0x10x10485720x104857130x2[3/4]0x45 |}]

let%test_unit "testPointeur10" =
  try 
    let _ = runtam (pathFichiersRat^"testPointeur10.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int, Pointeur(Undefined)) -> ()

let%test_unit "testPointeur11" =
  try 
    let _ = runtam (pathFichiersRat^"testPointeur11.rat")
    in raise ErreurNonDetectee
  with
  | AccesAdresseInvalide("a") -> ()

let%test_unit "testPointeur12" =
  try 
    let _ = runtam (pathFichiersRat^"testPointeur12.rat")
    in raise ErreurNonDetectee
  with
  | AccesAdresseInvalide("f1") -> ()



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
