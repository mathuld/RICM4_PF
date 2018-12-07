#load "dynlink.cma";;
#load "camlp4/camlp4o.cma" ;;

type oper2 = 
  | Moins
  | Plus
  | Mul
  | Div

type expr = 
  | Int of int
  | Op2 of oper2 * expr * expr
  | Bool of bool

let rec eval e =
  match e with
  | Int n -> n
  | Bool b -> b
  | Op2 (Moins, x, y) -> eval x - eval y
  | Op2 (Plus, x, y) -> eval x + eval y
  | Op2 (Mul, x, y) -> eval x * eval y
  | Op2 (Div, x, y) -> eval x / eval y

(* Impression avec toutes les parenthèses explicites *)
let string_oper2 o =
  match o with
  | Moins -> "-"
  | Plus -> "+"
  | Mul -> "*"
  | Div -> "/"

let rec print_expr e =
  match e with
  | Int n -> print_int n
  | Bool b -> print_string (string_of_bool b)
  | Op2 (o, x, y) ->
     (print_char '(';
      print_expr x;
      print_string (string_oper2 o);
      print_expr y;
      print_char ')')

(* FLOTS *)

(* Pour le test *)
let rec list_of_stream = parser
                       | [< 'x; l = list_of_stream >] -> x :: l
                       | [< >] -> []

(* ANALYSEUR LEXICAL sur un flot de caractères *)
	      
(* Schéma de Horner *)
let valchiffre c = int_of_char c - int_of_char '0'
let rec horner n = parser 
  | [< '  '0'..'9' as c; s >] -> horner (10 * n + valchiffre c) s
  | [< >] -> n

let rec chaine c = parser
                 | [< '  'a'..'z'|'A'..'Z' as n; s >] -> chaine c@[n] s
                 | [< >] -> c
           
(* test *)
let _ = horner 0 (Stream.of_string "45089")

(* Type des lexèmes *)
type token = 
  | Tent of int
  | Tmoins
  | Tplus
  | Tparouvre
  | Tparferme
  | Tmul
  | Tdiv
  | Tid of char list

(* 
Pour passer d'un flot de caractères à un flot de lexèmes,
on commence par une fonction qui analyse lexicalement les
caractères d'un lexème au début d'un flot de caractères.
La fonction next_token rend un token option, c'est-à-dire :
- soit Some (tk)   où tk est un token
  dans le cas où le début du flot correspond lexème
- soit None

Le type option est prédéfini ainsi dans la bibliothèque standard OCaml :
type 'a option =
  | None           (* indique l'absence de valeur *)
  | Some of 'a     (* indique la présence de valeur *)
*)
      
let rec next_token = parser
  | [< '  ' '|'\n'; tk = next_token >] -> tk (* élimination des espaces *)
  | [< '  '0'..'9' as c; n = horner (valchiffre c) >] -> Some (Tent (n))
  | [< '  '-' >] -> Some (Tmoins)
  | [< '  '+' >] -> Some (Tplus)
  | [< '  '(' >] -> Some (Tparouvre)
  | [< '  ')' >] -> Some (Tparferme)
  | [< '  '*' >] -> Some (Tmul)
  | [< '  '/' >] -> Some (Tdiv)
  | [< '  'a'..'z' | 'A'..'Z' as c; s = chaine c >] -> Some (Tid (s))
  | [< >] -> None

(* tests *)
let s = Stream.of_string "45 - - 089"
let tk1 = next_token s
let tk2 = next_token s
let tk3 = next_token s
let tk4 = next_token s
let tk5 = next_token s
let tk6 = next_token s

(* L'analyseur lexical parcourt récursivement le flot de caractères s
   en produisant un flot de lexèmes *)
let rec tokens s =
  match next_token s with
  | None -> [< >]
  | Some tk -> [< 'tk; tokens s >]

let lex s = tokens s

(* tests *)
let s = Stream.of_string "45 - - 089"
let stk = lex s
let ltk = list_of_stream stk  

(*
Alternativement, la primitive Stream.from conduit au même résultat,
on l'utilise comme ci-dessous.
*)

let lex s = Stream.from (fun _ -> next_token s)

(*
A savoir : cette dernière version repose sur une représentation
interne des flots beaucoup plus efficace. Pour plus de détails
sur Stream.from, consulter le manuel OCaml.
Dans un compilateur réaliste devant traiter de gros textes, 
c'est la version à utiliser.
*)

let ltk1 = list_of_stream (lex (Stream.of_string "356 - 10 - 4"))

(* ANALYSEUR SYNTAXIQUE sur un flot de lexèmes *)

(* A noter : le passage d'un argument de type expr pour obtenir le
   bon parenthèsage de l'expression :
   41 - 20 - 1 est compris comme (41 - 20) - 1, non pas 41 - (20 - 1)
*)

let rec p_expr = parser
               | [< t = p_terme; e = p_s_add t >] -> e
and p_s_add a = parser 
              | [< ' Tmoins; t = p_terme; e = p_s_add (Op2(Moins,a,t)) >] -> e
              | [< ' Tplus; t = p_terme; e = p_s_add (Op2(Plus,a,t)) >] -> e
              | [< >] -> a
and p_terme = parser
            | [< p = p_fact; e = p_s_mul p >] -> e

and p_s_mul a = parser
              | [< ' Tmul; t = p_fact; e = p_s_mul (Op2(Mul,a,t)) >] -> e
              | [< ' Tdiv; t = p_fact; e = p_s_mul (Op2(Div,a,t)) >] -> e
              | [< >] -> a

and p_fact = parser
            | [< ' Tent(n)>] -> Int(n)
            | [< ' Tparouvre; exp = p_expr; ' Tparferme>] -> exp
      
let ast s = p_expr (lex (Stream.of_string s))

let e1 = ast "1 - 2 * ( 4 + 6 / 2 )"
     
let _ = eval e1
let _ = print_expr e1
