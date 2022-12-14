open Type
open Ast.AstSyntax

(* Exceptions pour la gestion des identificateurs *)
exception DoubleDeclaration of string
exception IdentifiantNonDeclare of string
exception ContinueHorsLoop of string
exception BreakHorsLoop of string
exception MauvaiseUtilisationIdentifiant of string
exception AccesAdresseInvalide of string

(* Exceptions pour le typage *)
(* Le premier type est le type réel, le second est le type attendu *)
exception TypeInattendu of typ * typ
exception TypesParametresInattendus of typ list * typ list
exception TypeBinaireInattendu of binaire * typ * typ (* les types sont les types réels non compatible avec les signatures connues de l'opérateur *)
exception TypesRetourIncompatibles of typ * typ       (* les types réels renvoyés non compatibles -> devraient être les mêmes *)

(* Utilisation illégale de return dans le programme principal *)
exception RetourDansMain

(* Utilisation d'une fonction sans return *)
exception FonctionSansRetour of string (* nom de la fonction concerée *)