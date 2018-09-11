all:
	ocamlfind query elpi > /dev/null
	ocamllex lexer.mll
	ocamlyacc -v parser.mly
	ocamlfind opt -package ppx_import,ppx_deriving.std -c ast.ml
	ocamlfind opt -c parser.mli
	ocamlfind opt -c lexer.ml
	ocamlfind opt -c parser.ml
	ocamlfind opt -c pmap.ml
	ocamlfind opt -package elpi,ppx_import,ppx_deriving.std -linkpkg ast.cmx lexer.cmx parser.cmx pmap.cmx toyml.ml -o toyml
