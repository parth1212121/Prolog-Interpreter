make:
	ocamllex lexer.mll
	ocamllex lexer_goal.mll
	ocamlyacc parser.mly
	ocamlyacc parser_goal.mly
	ocamlc -c syntax.ml parser.mli  parser_goal.mli lexer.ml lexer_goal.ml parser.ml  parser_goal.ml main.ml
	ocamlc -o my_program lexer.cmo lexer_goal.cmo  parser.cmo parser_goal.cmo syntax.cmo main.cmo
	./my_program


clean:
	rm -f lexer.ml lexer_goal.ml parser.ml parser.mli parser_goal.ml parser_goal.mli lexer.cmi lexer.cmo lexer_goal.cmi lexer_goal.cmo parser.cmi parser.cmo parser_goal.cmi parser_goal.cmo  syntax.cmi syntax.cmo main.cmi main.cmo
	rm -f ./my_program
