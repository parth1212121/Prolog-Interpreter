open Lexer
open Lexer_goal
open Parser
open Parser_goal
open Syntax

open List;; 
type symbol = string * int;;  

type tree = V of string 
          | C of {node: symbol; children: tree list};; 

exception NotPossible;;

open Set;;
open String;;
module StringSet = Set.Make(String);;   

let rec print_term = function
| VARIABLES v -> Printf.printf "%s" v
| CONSTANT c -> Printf.printf "%d" c
| FunctionSymbol("_empty_list", []) -> Printf.printf " [] "
| FunctionSymbol("_list", [t1; FunctionSymbol("_empty_list", [])]) -> 
                                Printf.printf " [";
                                print_term t1;
                                Printf.printf "] ";
| FunctionSymbol("_list", [t;x]) -> (
    Printf.printf " [";
    print_term t;
    Printf.printf ",";
    print_list_body x;
    Printf.printf "] ";
  )
| FunctionSymbol(s, []) -> Printf.printf " %s " s

| STRING_CONSTANT c -> Printf.printf "%s" c
| FunctionSymbol (f, args) ->
    let n = List.length args in
    Printf.printf "%s("  f;
    List.iteri (fun i arg -> print_term arg; if i < n-1 then print_string ", ") args;
    Printf.printf ")"


and print_list_body = function
|  FunctionSymbol("_empty_list", []) -> Printf.printf ""
| FunctionSymbol("_list", [t1; FunctionSymbol("_empty_list", [])]) -> print_term t1
| FunctionSymbol("_list", [t1; t2]) -> (
print_term t1;
Printf.printf ",";
print_list_body t2;
)
| _ -> Printf.printf "";;


let print_tup x = match x with 
(var,term) ->
Printf.printf "%s" var;
Printf.printf " = ";
print_term term;
Printf.printf "\n";;

let rec print_substitution sub=  
List.iter print_tup sub;;


let print_atomic_formula = function
| PredicateSymbol (predicate, terms) -> 
  let n = List.length terms in
  Printf.printf "ATOMIC_FORMULA(%d" n;
  Printf.printf "-ARY_PREDICATE_SYMBOL (%s); [" predicate;
  List.iteri (fun i term -> print_term term; if i < n-1 then print_string ", ") terms;
  Printf.printf "])";
| ConstantAtomicFormula term ->
  Printf.printf "ATOMIC_FORMULA([";
  print_term term;
  Printf.printf "])";
| Cut -> 
  Printf.printf "ATOMIC_FORMULA([  !(CUT)  ])";;



let print_fact  = function
  
Fact head ->
 Printf.printf  "FACT-->  \n\t\t(HEAD -->\n\t\t\t(";
 print_atomic_formula  head;    
 Printf.printf  ")\n\t\t)";


and print_rule = function
| Rule (atomic_formula, body) ->
  Printf.printf  "RULE-->  \n\t\t(HEAD  -->\n\t\t\t(";
  print_atomic_formula atomic_formula;
  Printf.printf ")\n\t\t)\n\t\t";
  print_string "(BODY --> \n\t\t\t{ ";
  let len = List.length body in
  List.iteri (fun i atomic_formula ->
      print_atomic_formula atomic_formula;
      if i < len - 1 then print_string ", "
  ) body;
  Printf.printf " }\n\t\t)";;



let print_clause = function
    | FactClause fact ->
        Printf.printf "CLAUSE (FACT) --> \n\t[";
        print_fact fact;
        print_endline "\n\t]\n"
    | RuleClause rule ->
      Printf.printf "CLAUSE (RULE) --> \n\t[";
      print_rule rule;
      print_endline "\n\t]\n"
  


let rec print_program program =
    List.iter print_clause program

let rec vars t =
    match t with
    | VARIABLES x -> StringSet.singleton x 
    | CONSTANT _ -> StringSet.empty  
    | STRING_CONSTANT _ -> StringSet.empty  
    | FunctionSymbol(_, terms) ->
        List.fold_left (fun acc term -> StringSet.union acc (vars term)) StringSet.empty terms;;


let rec var_atm atom = match atom with

        PredicateSymbol(x,terms) -> 
            List.fold_left (fun acc term -> StringSet.union acc (vars term)) StringSet.empty terms
        | ConstantAtomicFormula(term) -> vars term
        |_ -> StringSet.empty
;;

let rec var_goal goal = match goal with

[] -> StringSet.empty 
| (x::xs) -> 
        List.fold_left (fun acc atom -> StringSet.union acc (var_atm atom)) (var_atm x) xs;; 



let rec find tbl x = match tbl with
      []-> false;
      | (s,t)::xs -> if s =x then 
                    true
                    else
                    find xs x;;

let rec efficient_compose_subst tb1 tb2 =                          (* O(n2) *) (* Becauese of "find" (if we use hash this is O(n))*)

        let rec helper  acc tb1 tb2 = match tb1, tb2 with

        [],[]-> acc
        | tb1,[] -> acc @ tb1
        | tb1,((x1,t1)::xs) -> if (find tb1) x1 then
                                helper acc tb1 xs
                                else
                                helper ((x1,t1)::acc) tb1 xs

        in
        helper [] tb1 tb2;;





let rec subst subst_table term =  match term with

| VARIABLES xjt -> 


    apply subst_table subst_table xjt  
| CONSTANT x -> term
| STRING_CONSTANT x -> term
| FunctionSymbol(x,terms)-> 
        let new_terms = List.map (subst subst_table) terms in
            FunctionSymbol(x,new_terms);

and  apply table table_og xjt = match table with   
    []-> VARIABLES xjt 
    | (s,t)::xs -> if s=xjt  then
                        begin
                        subst table_og t

                        end
                    else
                        apply xs table_og xjt;;
               

let rec apply_subst_term_list subst_table term_list = match term_list with

[]-> []
| (term1:: rest_terms) -> (subst subst_table term1) :: apply_subst_term_list subst_table rest_terms;;


let rec apply_sub_atom subst_table atom = match atom with

    PredicateSymbol(func,term_list) -> PredicateSymbol(func, apply_subst_term_list subst_table term_list)
    | ConstantAtomicFormula(term1) -> ConstantAtomicFormula(subst subst_table term1)
    | _ -> atom;;



let rec apply_sub_body subst_table body = match body with

    [] -> body
    | (atom1 :: rest_body) ->  (apply_sub_atom subst_table atom1) :: rest_body;;


let rec mgu_term t1 t2 substitution =   (* Always when called substitutions = [] therefore itrs just waste.*)
  let rec loop sub_table terms1 terms2 =
    match terms1, terms2 with
    | [], [] -> Some sub_table 
    | term1 :: rest1, term2 :: rest2 ->
        begin
          match mgu_term (subst sub_table term1) (subst sub_table term2) sub_table with
            | Some new_sub_table ->
                loop (efficient_compose_subst sub_table new_sub_table) rest1 rest2
            | None -> None 
        end
    | _ -> None
  in
  match t1, t2 with
  | VARIABLES x, VARIABLES y ->
      if x = y then Some substitution 
      else Some  ((x, VARIABLES y)::substitution) 
  | VARIABLES x, _ ->
      if StringSet.mem x (vars t2) then None 
      else Some  ((x, t2):: substitution) 
  | _, VARIABLES y ->
      if StringSet.mem y (vars t1) then None 
      else Some ((y, t1):: substitution) 
  | CONSTANT x, CONSTANT y ->
      if x = y then Some substitution
      else None 
  | STRING_CONSTANT x, STRING_CONSTANT y ->
        if x = y then Some substitution
        else None 
  | FunctionSymbol (x1, terms1), FunctionSymbol (x2, terms2) ->
      if x1 <> x2 then None 
      else loop substitution terms1 terms2 
  | _, _ -> None ;;




let rec atomic_formula_to_term atomic_formula =  match atomic_formula with

      | ConstantAtomicFormula(term) -> term
      | PredicateSymbol (x,terms) -> FunctionSymbol(x,terms)
      | _ -> failwith("wrong atomic formula") ;;


let mgu_atomic_formula at1 at2 = 

        let term1 = atomic_formula_to_term at1 in
            let term2 = atomic_formula_to_term at2 in
                mgu_term term1 term2;;


exception NOT_RESOLVABLE



let rec modify_term int_val term = match term with

    VARIABLES x -> VARIABLES (int_val ^ x)
    |FunctionSymbol(str,term_list) -> FunctionSymbol(str, List.map (modify_term int_val) term_list )
    | _ -> term
;;


let rec modify_atm  int_val atom = match atom with

PredicateSymbol(x,term_list) ->   PredicateSymbol(x, List.map (modify_term int_val) term_list)
| ConstantAtomicFormula(term) -> ConstantAtomicFormula(modify_term int_val term)
| _ -> atom
;;


let rec modify_clause cl int_val = match cl with

FactClause(Fact(head)) -> FactClause(Fact(modify_atm int_val head ))
| RuleClause(Rule(head,body ))-> 
                RuleClause(Rule(modify_atm int_val head , List.map (modify_atm int_val) body));;


let pred_of_atom atm = match atm with

PredicateSymbol (x, _) -> x
|ConstantAtomicFormula(t) ->
    begin
        match t with
        FunctionSymbol(str,_) -> str
        |_ -> "const"
    end
|_-> "_cut";;


let read_input_character () =
    print_string "Enter char: ";
    flush stdout;
    let input_line1 = input_line stdin in
    if String.length input_line1 = 0 then
        failwith "Nothing entered!!! "
    else
        input_line1.[0];;

let rec modify_prog program a = match program with
[]-> []
| focus_clause ::rest ->            
                 match focus_clause with

                 FactClause(Fact(head)) -> if  (pred_of_atom head) = (pred_of_atom a) then
                                            (modify_clause focus_clause "$$") :: (modify_prog rest a)
                                            else
                                            focus_clause::  (modify_prog rest a)

                | RuleClause(Rule(head,body)) -> if  (pred_of_atom head) = (pred_of_atom a) then
                                            (modify_clause focus_clause "$$") :: (modify_prog rest a)
                                            else
                                            focus_clause::  (modify_prog rest a);;



let is_member element string_set =
    StringSet.mem element string_set


let rec purify_sub subst1 subst_og var_goal = match subst1 with              (* CHANGE IT HERE!!! *)
[]-> []
| (x::xs) -> let (v,_) = x in
             if (is_member v var_goal) then
                let y = subst subst_og (VARIABLES v) in
                ((v,y ):: (purify_sub  xs subst_og var_goal))
             else
                (purify_sub xs subst_og var_goal)
;;


exception NOT_UNIFIABLE;;
exception ERROR2;;
  

let rec simplify_term  t = match t with
    CONSTANT(n)-> t
  | FunctionSymbol("+", [t1; t2]) -> 
    
    (
      match ((simplify_term t1), (simplify_term t2)) with
          (CONSTANT(n1), CONSTANT(n2)) -> CONSTANT(n1 + n2)
        | _ -> raise ERROR2
    )
  | FunctionSymbol("-", [t1; t2]) -> 
   
    (
      match ((simplify_term t1), (simplify_term t2)) with
          (CONSTANT(n1), CONSTANT(n2)) -> CONSTANT(n1 - n2)
        | _ -> raise  ERROR2
    )
  | FunctionSymbol("*", [t1; t2]) -> 
    
    ( 
      match ((simplify_term t1), (simplify_term t2)) with
          (CONSTANT(n1), CONSTANT(n2)) -> CONSTANT(n1 * n2)
        | _ -> raise  ERROR2
    )
  | FunctionSymbol("/", [t1; t2]) -> (
      match ((simplify_term t1), (simplify_term t2)) with
          (CONSTANT(n1), CONSTANT(n2)) -> CONSTANT(n1 / n2)
        | _ -> raise  ERROR2
      )
  | _ -> t
;;



let eval a unif= match a with
    PredicateSymbol("_eq", [t1; t2]) ->
                                            let term1 = (simplify_term (subst unif t1)) in
                                            let term2 = (simplify_term (subst unif t2)) in
                                            begin
                                            match (mgu_term term1 term2 []) with
                                            Some sub -> Some (efficient_compose_subst unif sub)
                                            | None -> None
                                            end
|     PredicateSymbol("not_eq", [t1; t2]) ->
                                            let term1 = (simplify_term (subst unif t1)) in
                                            let term2 = (simplify_term (subst unif t2)) in
                                            begin
                                            match (mgu_term term1 term2 []) with
                                            Some sub -> Some (efficient_compose_subst unif sub)
                                            | None -> None
                                            end
  | PredicateSymbol(">", [t1; t2]) -> (
        match (simplify_term (subst unif t1), simplify_term (subst unif t2)) with
            (CONSTANT(n1), CONSTANT(n2)) -> if n1 > n2 then Some unif else None
          | _ -> None
    )
  | PredicateSymbol("<", [t1; t2]) -> (
      match (simplify_term (subst unif t1), simplify_term (subst unif t2)) with
          (CONSTANT(n1), CONSTANT(n2)) -> if n1 < n2 then Some unif else None
        | _ -> None
    )
  | _ -> Some unif
;;



let rec resolve program goal substitutions var_set= match goal with

[]->                
    print_endline"Result: True";
    print_substitution  ( purify_sub substitutions substitutions var_set  );  (*  write the purify function!!!  ( CAN ALSO BE REMOVED!!! )  *)
    let choice = ref (read_input_character()) in
    while(!choice <> '.' && !choice <> ';') do
    Printf.printf "Please enter character letter (; and . are allowed) \n ";
    choice := read_input_character();     
    done;
    Printf.printf "\n";
    begin
    match !choice with
    '.' -> Some substitutions
    | _ -> None
    end;

| subgoal :: rest -> 

    begin
    match subgoal with        
    PredicateSymbol("_eq", _) | PredicateSymbol("<", _) | PredicateSymbol(">", _) -> 

        begin
        match (eval subgoal substitutions) with

        Some sub -> 
            begin
                match (resolve program rest sub var_set) with
                Some high_sub -> Some high_sub
                | None -> None
            end      
        | None -> None

        end

        |PredicateSymbol("not_eq", _) -> 

            begin
            match (eval subgoal substitutions) with
    
            None ->
                begin
                    match (resolve program rest substitutions var_set) with
                    Some high_sub -> Some high_sub
                    | None -> None
                end      
            | Some sub -> None
    
            end
            

    | PredicateSymbol("_cut", _) -> let _ = resolve program rest  substitutions var_set in Some substitutions

    | _ ->

    let rec unify_program try_clauses = match try_clauses with
    
    []-> None;     
    | focus_clause :: rest_clauses -> 
            match focus_clause with                        
            FactClause(fact)-> 

                begin
                let Fact(head) = fact in
                    match mgu_atomic_formula (apply_sub_atom substitutions subgoal) (apply_sub_atom substitutions head) [] with 
                        None -> unify_program rest_clauses (*  BACKTRAKING!! *)
                        |  Some new_substitution -> begin
                          
                                match resolve (modify_prog program head) rest (efficient_compose_subst substitutions new_substitution)  var_set with
                                    None -> unify_program rest_clauses  (*  BACKTRAKING!! *)
                                    | Some high_subtitution -> Some high_subtitution  
                            end    (* JUST CHANGE THE PROGRAM HERE!!! *)              
                end

            | RuleClause(rule) -> 

                begin

                let Rule(head,body) = rule in
                
                    match mgu_atomic_formula  (apply_sub_atom substitutions subgoal) (apply_sub_atom substitutions head) [] with 
                        None -> unify_program rest_clauses 
                        | Some new_substitution -> begin
                                                        match resolve (modify_prog program head) ((apply_sub_body (efficient_compose_subst substitutions new_substitution) body) @ rest) (efficient_compose_subst substitutions new_substitution)  var_set with
                                                            None -> unify_program rest_clauses  (*  BACKTRAKING!! *)
                                                            | Some high_subtitution -> Some high_subtitution  
                                                    end
                end 
    in       
                             
    unify_program program

    end;;


 let main =
    try
        while true do
        print_endline "ENTER A PROGRAM:";
        let input = read_line () in
        let lexbuf = Lexing.from_string input in
        let program = Parser.program Lexer.token lexbuf in
        
        print_endline "ENTER A GOAL:";
        let input2 = read_line () in
        let lexbuf2 = Lexing.from_string input2 in
        let goal = Parser_goal.goal Lexer_goal.token lexbuf2 in
        
        match resolve program goal [] (var_goal goal) with
        | Some substitutions ->
            print_endline "";
        | None ->  
            print_endline "Result: false";
        done
    with End_of_file -> ()





(* TESTCASES---->  *)  (* Fisrt line contains Program , Second line contains goal.*)


    (* 
    
    
    
    
    ho(1).kk(X):-ho(X).
    kk(1)
        Result: True
    
    
    
    
    
    ho(1).ho(2).ho(3).ho(4).
    ho(X)
    
        Result: True
        X = 1
        Enter char: ;
    
        Result: True
        X = 2
        Enter char: ;
    
        Result: True
        X = 3
        Enter char: ;
    
        Result: True
        X = 4
    
    
    hi(1,[2,3,4,5]):-!.
    hi(1,[2,3,X,5])
    
        Result: True
        X = 4
    
    
    hi(a,b,c).hi(c,b,a).hi(d,d,d).
    hi(A,B,C)
    
        Result: True
        A = a
        B = b
        C = c
        Enter char: ;
    
        Result: True
        A = c
        B = b
        C = a
        Enter char: ;
    
        Result: True
        A = d
        B = d
        C = d
    
    
    see(1,2).see(A,B).kk(B).kk(5).chk(A).
    chk(5)
    
        Result: True
    

        
    abc(X) :- grey(X), car(X).abc(X) :- sky(X), ground(X).car(1).car(2).ground("nice").grey(1).grey(2).sky("nice").
    abc(M)
    
    
        Result: True
        M = 1
        Enter char: ;
    
        Result: True
        M = 2
        Enter char: ;
    
        Result: True
        M = "nice"
    
    
    fact(0,1).fact(X,H):-X>0,Z=X-1,fact(Z,W),H=W*X.
    fact(7,A)
    
        Result: True
        A = 5040
    
    
    
    
    power2(0, 1).power2(X, R) :-X > 0,Z = X -1 ,power2(Z,PR),R =PR*2.
    power2(5,M)
    
        Result: True
        M = 32
        
    
    my_length([], 0).my_length([R|T], Length) :-my_length(T, PrevLength),Length = PrevLength + 1.
    my_length([1,2,3,4,5],M)
    
        Result: True
        M = 5
        
        
    pipe([1|[2|[3,4]]]).
    pipe([1,X,Y,Z])
    
        Result: True
        X = 2
        Z = 4
        Y = 3
    
    
    mem(X,[X|R]):-!. mem(X,[Y|R]):-mem(X,R).
    mem(1,[2,3,5,1,6,7])
    
        Result: True
    
    
    
    del(X,[],[]):- !.del(X,[X|R],Z):-del(X,R,Z),!.del(X,[Y|R],[Y|Z]):-del(X,R,Z),!.
    del(2,[1,3,4,2,6],M)
    
    
        Result: True
        M =  [1,3,4,6] 
    
    
    
    append([],L2,L2) :- !.append([X|R],L2,[X|M]) :- append(R,L2,M),!.
    append([1,2,3],[4,5,6],T)
    
    
        Result: True
        T =  [1,2,3,4,5,6]
    
    
    
    mem(X,[X|R]):-!. mem(X,[Y|R]):-mem(X,R).intersection([], M, []).intersection([H|T], List2, [H|Result]) :-mem(H, List2),intersection(T, List2, Result).intersection([J|T], List2, Result) :-intersection(T, List2, Result).
    intersection([1,2,3],[2,3,4,5,6],G)
    
        Result: True
        G =  [2,3]
    
    
    append([],L2,L2) :- !.append([X|R],L2,[X|M]) :- append(R,L2,M),!.reverse([], []).reverse([I|Xs], Rev) :-reverse(Xs, Rest),append(Rest, [I], Rev).
    reverse([1,2,3,4,5],ANS)
    
        Result: True
        ANS =  [5,4,3,2,1] 



     *)