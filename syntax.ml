 
(* ABSTRACT_SYNTAX OF THE COOL *)



type term = VARIABLES of string
          | CONSTANT of int
          | STRING_CONSTANT of string
          | FunctionSymbol of string * term list


type atomic_formula = PredicateSymbol of string * term list
                    | ConstantAtomicFormula of term
                    | Cut

type goal = atomic_formula list

type body = atomic_formula list

type head = atomic_formula

type rule = Rule of head * body

type fact = Fact of head

type clause = RuleClause of rule
            | FactClause of fact 


type program = clause list 