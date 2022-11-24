open Rat
open Compilateur
open Exceptions

exception ErreurNonDetectee

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../../tests/gestion_id/sans_fonction/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

let%test_unit "testAffectation1" = 
  let _ = compiler (pathFichiersRat^"src-rat-tds-test/testAffectation1.rat") in ()

let%test_unit "testAffectation2"= 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testAffectation2.rat") 
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("y") -> ()

let%test_unit "testAffectation3" = 
  let _ = compiler (pathFichiersRat^"src-rat-tds-test/testAffectation3.rat") in ()

let%test_unit "testAffectation4" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testAffectation4.rat")
    in raise ErreurNonDetectee
  with
  | MauvaiseUtilisationIdentifiant("x") -> ()

let%test_unit "testUtilisation1" = 
  let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation1.rat") in ()

let%test_unit "testUtilisation2" = 
  let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation2.rat") in ()

let%test_unit "testUtilisation3" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation3.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("y") -> ()

let%test_unit "testUtilisation10" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation10.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("x") -> ()

let%test_unit "testUtilisation11" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation11.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("z") -> ()

let%test_unit "testUtilisation12" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation12.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("z") -> ()

let%test_unit "testUtilisation13" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation13.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("z") -> ()

let%test_unit "testUtilisation14" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation14.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("z") -> ()

let%test_unit "testUtilisation15" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation15.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("z") -> ()

let%test_unit "testUtilisation16" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation16.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("y") -> ()

let%test_unit "testUtilisation17" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation17.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("y") -> ()

let%test_unit "testUtilisation18" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation18.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("y") -> ()

let%test_unit "testUtilisation19" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testUtilisation19.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("y") -> ()

let%test_unit "testRecursiviteVariable" = 
  try 
    let _ = compiler (pathFichiersRat^"src-rat-tds-test/testRecursiviteVariable.rat")
    in raise ErreurNonDetectee
  with
  | IdentifiantNonDeclare("x") -> ()

(* Fichiers de tests de la génération de code -> doivent passer la TDS *)

let%test_unit "code_testprintint" = 
let _ = compiler  (pathFichiersRat^"src-rat-tam-test/testprintint.rat") in ()

let%test_unit "code_testprintbool" = 
let _ = compiler  (pathFichiersRat^"src-rat-tam-test/testprintbool.rat") in ()

let%test_unit "code_testprintrat" = 
let _ = compiler  (pathFichiersRat^"src-rat-tam-test/testprintrat.rat") in ()

let%test_unit "code_testaddint" = 
let _ = compiler  (pathFichiersRat^"src-rat-tam-test/testaddint.rat") in ()

let%test_unit "code_testaddrat" = 
let _ = compiler  (pathFichiersRat^"src-rat-tam-test/testaddrat.rat") in ()

let%test_unit "code_testmultint" = 
let _ = compiler  (pathFichiersRat^"src-rat-tam-test/testmultint.rat") in ()

let%test_unit "code_testmultrat" = 
let _ = compiler  (pathFichiersRat^"src-rat-tam-test/testmultrat.rat") in ()

let%test_unit "code_testnum" = 
let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testnum.rat") in ()

let%test_unit "code_testdenom" = 
let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testdenom.rat") in ()

let%test_unit "code_testwhile1" = 
let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testwhile1.rat") in ()

let%test_unit "code_testif1" = 
let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testif1.rat") in ()

let%test_unit "code_testif2" = 
let _ = compiler   (pathFichiersRat^"src-rat-tam-test/testif2.rat") in ()

let%test_unit "code_factiter" = 
  let _ = compiler   (pathFichiersRat^"src-rat-tam-test/factiter.rat") in ()

