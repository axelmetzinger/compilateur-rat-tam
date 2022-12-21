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

let pathFichiersRat = "../../../../../tests/projet/loop/fichiersRat/"

(***********)
(*  TESTS  *)
(***********)

let%expect_test "testLoop1" =
  runtam (pathFichiersRat^"testLoop1.rat");
  [%expect{| 012345678910 |}]

let%expect_test "testLoop2" =
  runtam (pathFichiersRat^"testLoop2.rat");
  [%expect{| 1266645 |}]

  let%expect_test "testLoop3" =
    runtam (pathFichiersRat^"testLoop3.rat");
    [%expect{| 0001020304050607080901001101201301401501601701801902002102202302402502602702802903003103203303403503603703803904004104204304404504604704804905005105205305405505605705805910111213141516171819110111112113114115116117118119120121122123124125126127128129130131132133134135136137138139140141142143144145146147148149150151152153154155156157158159 |}]

let%expect_test "testLoop4" =
  runtam (pathFichiersRat^"testLoop4.rat");
  [%expect{| 0123456789101112131415161718192021222301234567891011121314151617181920212223 |}]

let%expect_test "testLoop5" =
  runtam (pathFichiersRat^"testLoop5.rat");
  [%expect{| 01234567891011121314151617181920212223 |}]

let%expect_test "testLoop5bis" =
  runtam (pathFichiersRat^"testLoop5bis.rat");
  [%expect{| 01234567891011121314151617181920212223 |}]

(* Dans ce test, le warning levé lors de la compilation concernant les loop de même nom
   se retrouve étrangement après le résultat d'exécution du programme. *)
let%expect_test "testLoop6" =
  runtam (pathFichiersRat^"testLoop6.rat");
  [%expect "000102030405060708091011121314151617181920212223242526272829\027[31m/!\\ Attention : loop de même nom imbriqués (`l`)\027[0m\n "]

(* Ici pas de warning car la boucle de même nom n'est pas dans la première *)
let%expect_test "testLoop6bis" =
  runtam (pathFichiersRat^"testLoop6bis.rat");
  [%expect {| 010 |}]


let%test_unit "testLoop7" =
  try 
    let _ = runtam (pathFichiersRat^"testLoop7.rat")
    in raise ErreurNonDetectee
  with
  | BreakHorsLoop _ -> ()

let%test_unit "testLoop8" =
try 
  let _ = runtam (pathFichiersRat^"testLoop8.rat")
  in raise ErreurNonDetectee
with
| ContinueHorsLoop _ -> ()



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
