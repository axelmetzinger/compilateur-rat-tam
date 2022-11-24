open Rat
open Compilateur
open Exceptions

exception ErreurNonDetectee

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/type/fichiersRat/"

(**********)
(*  TESTS *)
(**********)


let%test_unit "test2"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/test2.rat") in ()

let%test_unit "testAppel1"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel1.rat") in ()

let%test_unit "testAppel2"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel2.rat") in ()

let%test_unit "testAppel3"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel3.rat") in ()

let%test_unit "testAppel4"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel4.rat") in ()

let%test_unit "testAppel5"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel5.rat") in ()

let%test_unit "testAppel6"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel6.rat")
    in raise ErreurNonDetectee
  with
  | TypesParametresInattendus _ -> ()

let%test_unit "testAppel7"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel7.rat")
    in raise ErreurNonDetectee
  with
  | TypesParametresInattendus _ -> ()

let%test_unit "testAppel8"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel8.rat")
    in raise ErreurNonDetectee
  with
  | TypesParametresInattendus _ -> ()

let%test_unit "testAppel9"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel9.rat")
    in raise ErreurNonDetectee
  with
  | TypesParametresInattendus _ -> ()

let%test_unit "testAppel10"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel10.rat")
    in raise ErreurNonDetectee
  with
  | TypesParametresInattendus _  -> ()

let%test_unit "testAppel11"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel11.rat")
    in raise ErreurNonDetectee
  with
  | TypesParametresInattendus _  -> ()

let%test_unit "testAppel12"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel12.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Bool) -> ()

let%test_unit "testAppel13"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testAppel13.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Int,Rat) -> ()

let%test_unit "testRetourFonction1"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testRetourFonction1.rat") in ()

let%test_unit "testRetourFonction2"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testRetourFonction2.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Int) -> ()

let%test_unit "testRetourFonction3"=
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testRetourFonction3.rat") in ()

let%test_unit "testRetourFonction4"=
  try
    let _ = compiler (pathFichiersRat^"src-rat-type-test/testRetourFonction4.rat")
    in raise ErreurNonDetectee
  with
  | TypeInattendu(Bool,Int) -> ()

let%test_unit "testRecursiviteFonction"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/testRecursiviteFonction.rat") in ()

let%test_unit "test"= 
  let _ = compiler (pathFichiersRat^"src-rat-type-test/test.rat") in ()

let%test_unit "code_factrec" = 
let _ = compiler   (pathFichiersRat^"src-rat-tam-test/factrec.rat") in ()

(* Fichiers de tests de la génération de code -> doivent passer le typage *)

let%test_unit "code_testfun1" = 
  let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testfun1.rat") in ()

let%test_unit "code_testfun2" = 
  let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testfun2.rat") in ()

let%test_unit "code_testfun3" = 
  let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testfun3.rat") in ()

let%test_unit "code_testfun4" = 
  let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testfun4.rat") in ()

let%test_unit "code_testfun5" = 
  let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testfun5.rat") in ()

let%test_unit "code_testfun6" = 
  let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testfun6.rat") in ()

let%test_unit "code_testfuns" = 
let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testfuns.rat") in ()


