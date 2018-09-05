all:
	ocamlfind query elpi > /dev/null
	ocamlfind opt -package elpi -linkpkg mlwshop.ml -o mlwshop
